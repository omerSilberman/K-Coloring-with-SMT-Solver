#!/usr/bin/env python3
"""Write one SMT-LIB file per graph and encoding, to run solvers on them on the cluster.

For every graph in optimal_k_values.json with a known K, and every encoding of one
engine (cvc5 or Z3), this runs that engine's binary with --dump-smt2 to write the
K-coloring problem as an .smt2 file. It then writes the lab's benchmark-set files
(benchmark_set_<name>, one absolute path per line) for submit-job.sh.

Layouts (--layout):
  graph     OUT/<graph>/<family>/<encoding>_<graph>.smt2      (default)
  encoding  OUT/<family>/<encoding>/<encoding>_<graph>.smt2
<family> is the encoding's group in the GUI: int, bv, fp, real, real-trig, ff, dt-uf,
strings, arrays, bool, other, theory-independent.

K (--k-offset):
   0  the known K: every file is satisfiable                (default)
  -1  K-1: unsatisfiable when K is the chromatic number, so only graphs whose K is
      OPTIMAL are used, unless --include-feasible (their files are marked unknown)

Examples:
  cluster/gen_smt2.py                                    # cvc5, K, layout by graph
  cluster/gen_smt2.py --k-offset -1                      # cvc5, K-1
  cluster/gen_smt2.py --engine z3 --layout encoding
  cluster/gen_smt2.py --graphs 'myciel' --encodings '^BV' --out /tmp/try

Files that already exist are kept, so an interrupted run can be restarted (--force
rewrites them). Encodings that fail for a graph are listed in OUT/failures.tsv, and
OUT/manifest.tsv lists every file with its graph, K and expected answer.
"""
import argparse
import concurrent.futures
import json
import os
import re
import subprocess
import sys
import time

PROJECT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# The encoding groups, as in the GUI (family() in gui/static/app.js), as folder names
FAMILIES = [
    (r"^(LIA|IDL|INT-)", "int"),
    (r"^BV", "bv"),
    (r"^FP$", "fp"),
    (r"^NLRA-(SIN|COS)", "real-trig"),
    (r"^NLRA", "real"),
    (r"^FF-", "ff"),
    (r"^(LIST-|PEANO$|UF$|UF-)", "dt-uf"),
    (r"^STR", "strings"),
    (r"^ARR", "arrays"),
    (r"^BOOL-", "bool"),
]
GENERIC_FAMILY = "theory-independent"


def family(name, generic):
    if generic:
        return GENERIC_FAMILY
    for pattern, folder in FAMILIES:
        if re.search(pattern, name):
            return folder
    return "other"


def parse_args():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--engine", choices=["cvc5", "z3"], default="cvc5",
                    help="whose encodings and SMT-LIB dialect to use (default: cvc5)")
    ap.add_argument("--k-offset", type=int, default=0, help="use K + OFFSET colors, e.g. -1 (default: 0)")
    ap.add_argument("--include-feasible", action="store_true",
                    help="with a negative offset, also use graphs whose K is not known to be optimal")
    ap.add_argument("--layout", choices=["graph", "encoding"], default="graph",
                    help="folder structure (default: graph)")
    ap.add_argument("--sets", choices=["graph", "encoding"], default="graph",
                    help="one benchmark set per graph or per encoding (default: graph)")
    ap.add_argument("--elements", choices=["default", "all"], default="default",
                    help="theory-independent encodings: default element theory only, or every one")
    ap.add_argument("--graphs", metavar="REGEX", help="only graphs whose name matches REGEX")
    ap.add_argument("--encodings", metavar="REGEX", help="only encodings whose name matches REGEX")
    ap.add_argument("--json", default=os.path.join(PROJECT, "optimal_k_values.json"),
                    help="the K values (default: optimal_k_values.json)")
    ap.add_argument("--out", help="output folder (default: smt2/<engine>_k or smt2/<engine>_k-1 ...)")
    ap.add_argument("--sets-dir", help="where to write the benchmark_set_* files (default: OUT); "
                                       "submit-job.sh looks for them in the folder it is run from")
    ap.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1),
                    help="files to write at once (default: 4). Each can need several GB of memory "
                         "on the largest graphs")
    ap.add_argument("--timeout", type=float, default=600, help="seconds allowed per file (default: 600)")
    ap.add_argument("--force", action="store_true", help="rewrite files that already exist")
    return ap.parse_args()


def load_encodings(binary, elements_mode, pattern):
    """[(encoding name, family)] for every encoding the binary has"""
    listing = json.loads(subprocess.run([binary, "--list-json"], capture_output=True, text=True,
                                        check=True).stdout)
    encodings = []
    for e in listing["encodings"]:
        if not e["generic"]:
            encodings.append((e["name"], family(e["name"], False)))
            continue
        elements = listing["elements"] if elements_mode == "all" else [e["default_element"]]
        for element in elements:
            encodings.append((f"{e['name']}-{element}", family(e["name"], True)))
    if pattern:
        encodings = [(n, f) for n, f in encodings if re.search(pattern, n)]
    return encodings


def load_graphs(args):
    """[(graph name, absolute path, K to use, expected answer)]"""
    with open(args.json) as f:
        data = json.load(f)
    graphs, skipped_feasible = [], 0
    for path, value in data.items():
        k = value if isinstance(value, int) else value.get("k") if isinstance(value, dict) else None
        status = value.get("status") if isinstance(value, dict) else None
        if k is None or k + args.k_offset < 1:
            continue
        if args.k_offset >= 0:
            expected = "sat"
        elif status == "OPTIMAL":
            expected = "unsat"
        elif args.include_feasible:
            expected = "unknown"
        else:
            skipped_feasible += 1
            continue
        name = os.path.splitext(os.path.basename(path))[0]
        if args.graphs and not re.search(args.graphs, name):
            continue
        full_path = os.path.realpath(os.path.join(PROJECT, path))
        if not os.path.isfile(full_path):
            sys.exit(f"Error: graph file not found: {full_path}")
        graphs.append((name, full_path, k + args.k_offset, expected))
    if skipped_feasible:
        print(f"Skipped {skipped_feasible} graphs whose K is not known to be optimal "
              f"(K{args.k_offset:+d} might be satisfiable); --include-feasible uses them too")
    return graphs


def write_file(binary, encoding, graph_path, k, expected, target, timeout):
    """Writes one benchmark; returns None, or why it failed"""
    os.makedirs(os.path.dirname(target), exist_ok=True)
    partial = target + ".part"  # renamed when complete, so a stopped run leaves no half files
    try:
        run = subprocess.run([binary, encoding, graph_path, str(k), "--dump-smt2", partial, "--expected", expected],
                             capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        reason = f"took more than {timeout:g} s"
    else:
        if run.returncode == 0 and os.path.isfile(partial):
            os.replace(partial, target)
            return None
        lines = (run.stderr + run.stdout).strip().splitlines()
        reason = lines[-1] if lines else f"exit code {run.returncode}"
    if os.path.exists(partial):
        os.remove(partial)
    return reason


def main():
    args = parse_args()
    binary = os.path.join(PROJECT, "build", f"smt_solver_{args.engine}")
    if not os.access(binary, os.X_OK):
        sys.exit(f"Error: {binary} not found; build the project first")
    suffix = f"_k{args.k_offset:+d}" if args.k_offset else "_k"
    out = os.path.realpath(args.out or os.path.join(PROJECT, "smt2", args.engine + suffix))
    sets_dir = os.path.realpath(args.sets_dir or out)

    encodings = load_encodings(binary, args.elements, args.encodings)
    graphs = load_graphs(args)
    if not encodings or not graphs:
        sys.exit("Nothing to do: no encodings or no graphs selected")

    tasks = []  # (graph, encoding, family, graph path, K, expected, target)
    for graph, graph_path, k, expected in graphs:
        for encoding, fam in encodings:
            file_name = f"{encoding}_{graph}.smt2"
            if args.layout == "graph":
                target = os.path.join(out, graph, fam, file_name)
            else:
                target = os.path.join(out, fam, encoding, file_name)
            tasks.append((graph, encoding, fam, graph_path, k, expected, target))

    todo = [t for t in tasks if args.force or not os.path.isfile(t[6])]
    print(f"{args.engine}: {len(graphs)} graphs x {len(encodings)} encodings = {len(tasks)} files "
          f"({len(tasks) - len(todo)} already there), K{args.k_offset:+d}, into {out}", flush=True)

    failures = {}  # (graph, encoding) -> reason
    start, done = time.time(), 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = {pool.submit(write_file, binary, t[1], t[3], t[4], t[5], t[6], args.timeout): t for t in todo}
        for future in concurrent.futures.as_completed(futures):
            graph, encoding = futures[future][:2]
            reason = future.result()
            done += 1
            if reason:
                failures[(graph, encoding)] = reason
                print(f"  failed: {encoding} on {graph}: {reason}", flush=True)
            if done % 100 == 0 or done == len(todo):
                print(f"[{done}/{len(todo)}] {100 * done // len(todo)}%, {time.time() - start:.0f} s, "
                      f"{len(failures)} failed", flush=True)

    # The manifest, failures and benchmark sets cover every file there, old or new
    os.makedirs(out, exist_ok=True)
    os.makedirs(sets_dir, exist_ok=True)
    present = [t for t in tasks if os.path.isfile(t[6])]
    with open(os.path.join(out, "manifest.tsv"), "w") as f:
        f.write("graph\tk\texpected\tfamily\tencoding\tpath\n")
        for graph, encoding, fam, _, k, expected, target in present:
            f.write(f"{graph}\t{k}\t{expected}\t{fam}\t{encoding}\t{target}\n")
    with open(os.path.join(out, "failures.tsv"), "w") as f:
        f.write("graph\tencoding\treason\n")
        for (graph, encoding), reason in sorted(failures.items()):
            f.write(f"{graph}\t{encoding}\t{reason}\n")

    sets = {}
    for graph, encoding, _, _, _, _, target in present:
        sets.setdefault(graph if args.sets == "graph" else encoding, []).append(target)
    for name, paths in sets.items():
        with open(os.path.join(sets_dir, f"benchmark_set_{name}"), "w") as f:
            f.writelines(p + "\n" for p in sorted(paths))

    size = sum(os.path.getsize(t[6]) for t in present)
    print(f"\nDone: {len(present)} files ({size / 1e6:.1f} MB), {len(failures)} failed "
          f"(see failures.tsv), {len(sets)} benchmark sets in {sets_dir}")


if __name__ == "__main__":
    main()
