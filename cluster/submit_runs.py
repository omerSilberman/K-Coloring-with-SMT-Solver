#!/usr/bin/env python3
"""Run solver configurations on the cluster through the lab's submit-job.sh.

Each configuration of a benchmark.py solvers file (e.g. "BV cvc5": smt_solver_cvc5 BV)
becomes one submit-job.sh call, which runs that solver binary on every graph in parallel
(one Slurm array task per graph). The graphs go in one benchmark set, one line per
graph: "<graph path> <K>", which submit-job.sh's --multi option appends to the command:
  smt_solver_cvc5 BV --smtlib-result <graph path> <K>
--smtlib-result makes the solvers answer sat/unsat/unknown, the words cmpr.py reads.

Everything goes in RUNS/<tag>/ (default tag: <solvers file>_k, or _k-1 with --k-offset -1):
  benchmark_set_kcolor     the graphs and their K
  <configuration>/kcolor/  submit-job.sh's results, one folder per graph
and the script ends by printing the cmpr.py command that compares the configurations.

Examples (run on the cluster's login node, from anywhere):
  cluster/submit_runs.py --pilot                   # 2 configurations on 3 small graphs
  cluster/submit_runs.py                           # every configuration, every graph, K
  cluster/submit_runs.py --k-offset -1             # K-1 (unsatisfiable, optimal graphs only)
  cluster/submit_runs.py --solvers solvers_z3.conf --time-limit 300
  cluster/submit_runs.py --dry-run                 # check everything, submit nothing
"""
import argparse
import ast
import json
import os
import re
import subprocess
import sys

PROJECT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SUPPORTED = ("smt_solver_cvc5", "smt_solver_z3")  # binaries with the shared command line
SET_NAME = "kcolor"


def parse_args():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solvers", default="solvers_cvc5_vs_z3.conf",
                    help="solvers file, as for benchmark.py (default: solvers_cvc5_vs_z3.conf)")
    ap.add_argument("--only", metavar="REGEX", help="only configurations whose name matches REGEX")
    ap.add_argument("--graphs", metavar="REGEX", help="only graphs whose file name matches REGEX")
    ap.add_argument("--k-offset", type=int, default=0, help="use K + OFFSET colors, e.g. -1 (default: 0)")
    ap.add_argument("--include-feasible", action="store_true",
                    help="with a negative offset, also use graphs whose K is not known to be optimal")
    ap.add_argument("--pilot", action="store_true", help="only the first 2 configurations on the 3 smallest graphs")
    ap.add_argument("--time-limit", type=int, default=60, help="CPU seconds per run (default: 60)")
    ap.add_argument("--memory", type=int, default=8000, help="MB per run (default: 8000)")
    ap.add_argument("--runs", default=os.path.expanduser("~/work/runs"), help="results folder (default: ~/work/runs)")
    ap.add_argument("--tag", help="name of this batch of runs inside RUNS (default: from the options)")
    ap.add_argument("--json", default=os.path.join(PROJECT, "optimal_k_values.json"), help="the K values")
    ap.add_argument("--submit-job", default="/private/zohar-lab/scripts/submit-job.sh", help=argparse.SUPPRESS)
    ap.add_argument("--dry-run", action="store_true", help="pass --dry-run to submit-job.sh: check, submit nothing")
    return ap.parse_args()


def load_configurations(args):
    """[(folder name, binary, options)] of the configurations submit-job.sh can run"""
    path = args.solvers if os.path.isabs(args.solvers) else os.path.join(PROJECT, args.solvers)
    with open(path) as f:
        solvers = ast.literal_eval(f.read())
    configurations = []
    for solver in solvers:
        command = solver.get("bin_path")
        if not isinstance(command, list) or os.path.basename(command[0]) not in SUPPORTED:
            print(f"Skipping '{solver['name']}': only {' and '.join(SUPPORTED)} run through submit-job.sh")
            continue
        if args.only and not re.search(args.only, solver["name"]):
            continue
        binary = os.path.normpath(os.path.join(PROJECT, command[0]))
        if not os.access(binary, os.X_OK):
            sys.exit(f"Error: {binary} not found; build the project first")
        name = re.sub(r"[^A-Za-z0-9]+", "_", solver["name"]).strip("_")
        configurations.append((name, binary, command[1:] + ["--smtlib-result"]))
    if args.pilot:
        configurations = configurations[:2]
    return configurations


def load_graphs(args):
    """[(absolute graph path, K to use)]"""
    with open(args.json) as f:
        data = json.load(f)
    graphs, skipped = [], 0
    for path, value in data.items():
        k = value if isinstance(value, int) else value.get("k") if isinstance(value, dict) else None
        status = value.get("status") if isinstance(value, dict) else None
        if k is None or k + args.k_offset < 1:
            continue
        if args.k_offset < 0 and status != "OPTIMAL" and not args.include_feasible:
            skipped += 1
            continue
        if args.graphs and not re.search(args.graphs, os.path.basename(path)):
            continue
        full_path = os.path.realpath(os.path.join(PROJECT, path))
        if not os.path.isfile(full_path):
            sys.exit(f"Error: graph file not found: {full_path}")
        graphs.append((full_path, k + args.k_offset))
    if skipped:
        print(f"Skipped {skipped} graphs whose K is not known to be optimal (K{args.k_offset:+d} might be "
              f"satisfiable); --include-feasible uses them too")
    if args.pilot:
        graphs = sorted(graphs, key=lambda g: os.path.getsize(g[0]))[:3]
    return graphs


def main():
    args = parse_args()
    configurations = load_configurations(args)
    graphs = load_graphs(args)
    if not configurations or not graphs:
        sys.exit("Nothing to run: no configurations or no graphs selected")

    stem = os.path.splitext(os.path.basename(args.solvers))[0].removeprefix("solvers_")
    tag = args.tag or (stem + (f"_k{args.k_offset:+d}" if args.k_offset else "_k") + ("_pilot" if args.pilot else ""))
    batch = os.path.join(os.path.realpath(args.runs), tag)
    clashes = [name for name, _, _ in configurations if os.path.exists(os.path.join(batch, name))]
    if clashes and not args.dry_run:
        sys.exit(f"Error: {batch} already has results for {', '.join(clashes)}. "
                 f"Choose another --tag, or move the old results away")

    # submit-job.sh finds benchmark sets in the folder it runs from, so it runs from here
    os.makedirs(batch, exist_ok=True)
    with open(os.path.join(batch, f"benchmark_set_{SET_NAME}"), "w") as f:
        f.writelines(f"{path} {k}\n" for path, k in graphs)
    print(f"{len(configurations)} configurations x {len(graphs)} graphs, K{args.k_offset:+d}, "
          f"{args.time_limit} s CPU and {args.memory} MB per run, into {batch}", flush=True)

    for name, binary, options in configurations:
        print(f"\n==> {name}: {os.path.basename(binary)} {' '.join(options)}", flush=True)
        command = [args.submit_job, binary, "--multi", "-o", " ".join(options),
                   "-t", str(args.time_limit), "-m", str(args.memory),
                   "-d", os.path.join(batch, name), "-b", SET_NAME, "-n", f"kc_{name}"]
        if args.dry_run:
            command.append("--dry-run")
        if subprocess.run(command, cwd=batch).returncode != 0:
            sys.exit(f"Error: submit-job.sh failed for {name}; the configurations after it were not submitted")

    if args.dry_run:
        print("\nDry run: nothing was submitted.")
        return
    print(f"""
All submitted. Check progress with:
  squeue -u $USER
When nothing of yours is left in the queue, compare the configurations with:
  /private/zohar-lab/scripts/cmpr.py --ignore-cache {batch}/*/{SET_NAME} -t""")


if __name__ == "__main__":
    main()
