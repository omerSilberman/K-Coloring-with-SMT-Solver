#!/usr/bin/env python3
"""Find the optimal K of many graphs at once on the cluster: one Slurm array task per graph.

Each task does what find_optimal_k.py does for one graph with an SMT encoding (default:
BV with cvc5): start from the best known coloring (optimal_k_values.json or DSATUR) and
ask for fewer colors until the solver proves it impossible (UNSAT) or times out. A task
saves its result after every solver answer, so a task stopped by Slurm's time limit
keeps what it found, and submitting again carries on from there.

Commands:
  submit   choose the graphs and submit the array job
  status   how many graphs are OPTIMAL / FEASIBLE / not done yet
  merge    write the results into a JSON file in the format of optimal_k_values.json

By default every graph that is not already OPTIMAL in optimal_k_values.json is tried:
FEASIBLE ones, the ones skipped as too large, and graphs that have no entry yet.

Examples (on the cluster's login node, in the project folder):
  cluster/find_k.py submit                          # BV, 30 min per solver call
  cluster/find_k.py submit --timeout 3600 --time 12:00:00
  cluster/find_k.py submit --graphs 'qwhdec' --tag qwh
  cluster/find_k.py status
  cluster/find_k.py merge                           # -> RUN/optimal_k_values.json
  cluster/find_k.py merge --in-place                # update the project's file (with a backup)
"""
import argparse
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import time

PROJECT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, PROJECT)
import find_optimal_k as fok  # noqa: E402  (parsing, bounds and solver calls)

K_FILE = os.path.join(PROJECT, "optimal_k_values.json")


def parse_args():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="command", required=True)
    for name in ("submit", "status", "merge", "task"):
        p = sub.add_parser(name)
        p.add_argument("--runs", default=os.path.expanduser("~/work/optimal_k"),
                       help="where the runs are kept (default: ~/work/optimal_k)")
        p.add_argument("--tag", help="this run's folder in RUNS (default: <theory>_<timeout>s)")
        p.add_argument("--theory", default="BV", help="encoding of smt_solver_cvc5 (default: BV)")
        p.add_argument("--timeout", type=float, default=1800, help="seconds per solver call (default: 1800)")
        if name == "submit":
            p.add_argument("--search", choices=["linear", "binary"], default="linear",
                           help="as in find_optimal_k.py (default: linear)")
            p.add_argument("--strategy", action="append", default=[], metavar="NAME[:PARAMS]",
                           help="strategy for every solver call (repeatable), as in find_optimal_k.py")
            p.add_argument("--graphs", metavar="REGEX", help="only graphs whose path matches REGEX")
            p.add_argument("--all", action="store_true", help="also graphs already OPTIMAL")
            p.add_argument("--benchmarks", default=os.path.join(PROJECT, "benchmarks"),
                           help="folder searched for .col/.clq graphs (default: benchmarks)")
            p.add_argument("--time", default="04:00:00", help="Slurm time limit per graph (default: 04:00:00)")
            p.add_argument("--mem", default="16G", help="memory per graph (default: 16G)")
            p.add_argument("--parallel", type=int, default=40, help="graphs running at once (default: 40)")
            p.add_argument("--partition", default="p_zohar")
            p.add_argument("--qos", help="Slurm QOS, if long jobs need one")
            p.add_argument("--dry-run", action="store_true", help="write the graph list, do not submit")
        if name == "merge":
            p.add_argument("--in-place", action="store_true",
                           help="update the project's optimal_k_values.json (backed up first)")
    args = ap.parse_args()
    args.tag = args.tag or f"{args.theory}_{args.timeout:g}s"
    args.dir = os.path.join(os.path.realpath(args.runs), args.tag)
    return args


def load_k_file():
    with open(K_FILE) as f:
        return json.load(f)


def result_path(run_dir, index, graph):
    return os.path.join(run_dir, "results", f"{index:04d}_{os.path.basename(graph)}.json")


def read_json(path):
    try:
        with open(path) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def write_json(path, data):
    partial = path + ".part"
    with open(partial, "w") as f:
        json.dump(data, f, indent=4)
    os.replace(partial, path)  # never a half-written file, even if the task is killed


# ----------------------------------------------------------------------------- submit
def submit(args):
    known = load_k_file()
    files = sorted(f for ext in ("*.col", "*.clq") for f in glob.glob(os.path.join(args.benchmarks, "**", ext),
                                                                           recursive=True))
    graphs = []
    for full in files:
        key = os.path.relpath(full, PROJECT)  # the key optimal_k_values.json uses
        entry = known.get(key)
        if not args.all and isinstance(entry, dict) and entry.get("status") == "OPTIMAL":
            continue
        if args.graphs and not re.search(args.graphs, key):
            continue
        graphs.append(key)
    if not graphs:
        sys.exit("No graphs to run: every selected graph is already OPTIMAL (--all runs them anyway)")

    os.makedirs(os.path.join(args.dir, "results"), exist_ok=True)
    os.makedirs(os.path.join(args.dir, "logs"), exist_ok=True)
    list_file = os.path.join(args.dir, "graphs.txt")
    if os.path.exists(list_file):
        with open(list_file) as f:
            old = f.read().split()
        if old != graphs:
            sys.exit(f"Error: {args.dir} holds a run with a different list of graphs. "
                     f"Use another --tag, or the same options as before to resume it")
    with open(list_file, "w") as f:
        f.writelines(g + "\n" for g in graphs)
    write_json(os.path.join(args.dir, "settings.json"),
               {"theory": args.theory, "timeout": args.timeout, "search": args.search, "strategies": args.strategy})

    done = sum(1 for i, g in enumerate(graphs, 1)
               if (read_json(result_path(args.dir, i, g)) or {}).get("status") == "OPTIMAL")
    print(f"{len(graphs)} graphs ({done} already OPTIMAL in this run, they finish at once), {args.theory}, "
          f"{args.timeout:g} s per solver call, {args.search} search, up to {args.time} and {args.mem} per graph, "
          f"{args.parallel} at once")
    command = ["sbatch", "--parsable", f"--array=1-{len(graphs)}%{args.parallel}", f"--partition={args.partition}",
               "--cpus-per-task=1", f"--mem={args.mem}", f"--time={args.time}", f"--job-name=optk_{args.theory}",
               f"--output={args.dir}/logs/%a.log", "--open-mode=append"]
    if args.qos:
        command.append(f"--qos={args.qos}")
    command += ["--wrap", f"python3 -u {os.path.abspath(__file__)} task --runs {args.runs} --tag {args.tag} "
                          f"--theory {args.theory} --timeout {args.timeout:g}"]
    if args.dry_run:
        print("Dry run, not submitted. The command would be:\n  " + " ".join(command))
        return
    job = subprocess.run(command, capture_output=True, text=True)
    if job.returncode != 0:
        sys.exit(f"sbatch failed: {job.stderr.strip()}")
    print(f"""Submitted job {job.stdout.strip()}. Follow it with:
  squeue -u $USER
  cluster/find_k.py status --tag {args.tag}
Each graph's log is {args.dir}/logs/<task number>.log; graph N is line N of {list_file}.""")


# ----------------------------------------------------------------------------- task
def run_task(args):
    index = int(os.environ["SLURM_ARRAY_TASK_ID"])
    settings = read_json(os.path.join(args.dir, "settings.json"))
    with open(os.path.join(args.dir, "graphs.txt")) as f:
        graph = f.read().split()[index - 1]
    out = result_path(args.dir, index, graph)
    previous = read_json(out) or {}
    if previous.get("status") == "OPTIMAL":
        print(f"{graph}: already OPTIMAL (K={previous['k']}), nothing to do")
        return

    print(f"=== {graph} ({time.strftime('%Y-%m-%d %H:%M:%S')}, host {os.uname().nodename})", flush=True)
    num_nodes, edges = fok.parse_dimacs(os.path.join(PROJECT, graph))
    print(f"{num_nodes} nodes, {len(edges)} edges", flush=True)
    adj = fok.build_adjacency(num_nodes, edges)
    dsatur_k = fok.dsatur_upper_bound(num_nodes, adj)
    clique = fok.greedy_clique_lower_bound(num_nodes, adj)
    print(f"DSATUR: {dsatur_k} colors, clique found: {clique} nodes", flush=True)

    # The best coloring known so far: this run's last save, the project's file, or DSATUR
    best_k, source = dsatur_k, "DSATUR"
    entry = load_k_file().get(graph)
    if isinstance(entry, dict) and entry.get("k") and entry["k"] < best_k:
        best_k, source = entry["k"], entry.get("source", "previous run")
    if previous.get("k") and previous["k"] < best_k:
        best_k, source = previous["k"], previous["source"]
    proven_low = max(clique, previous.get("proven_low", 0))  # every K below this is impossible
    proof = previous.get("proof") if previous.get("proven_low", 0) > clique else "clique"

    def save():
        status = "OPTIMAL" if proven_low >= best_k else "FEASIBLE"
        result = {"k": best_k, "status": status, "source": source}
        if status == "OPTIMAL":
            result["proof"] = proof
        result.update({"clique": clique, "solver": settings["theory"], "timeout": settings["timeout"]})
        write_json(out, dict(result, proven_low=proven_low, proof=proof, updated=time.strftime("%Y-%m-%d %H:%M:%S")))
        return status

    save()
    binary = os.path.join(PROJECT, "build", "smt_solver_cvc5")
    low = proven_low
    while low < best_k:
        k = best_k - 1 if settings["search"] == "linear" else (low + best_k) // 2
        command = [binary, settings["theory"], os.path.join(PROJECT, graph), str(k), "--model"]
        for strategy in settings["strategies"]:
            command += ["--strategy", strategy]
        started = time.time()
        print(f"K={k}" + ("" if settings["search"] == "linear" else f" (range {low}..{best_k})") + ": ",
              end="", flush=True)
        outcome, used = fok.smt_call(command, settings["timeout"], None)
        used = min(used or k, k)
        print(f"{fok.describe(outcome, used, k)} ({time.time() - started:.0f} s)", flush=True)
        if outcome == "SAT":
            best_k, source = used, "SAT"
        elif outcome == "UNSAT":
            low = k + 1
            if k + 1 > proven_low:
                proven_low, proof = k + 1, "UNSAT"
        elif settings["search"] == "linear":
            break  # a timeout or a crash: K-1 stays unresolved
        else:
            low = k + 1
        save()
    print(f"=> K={best_k}, {save()} ({time.strftime('%Y-%m-%d %H:%M:%S')})")


# ----------------------------------------------------------------------------- status / merge
def collect(args):
    """[(graph, result or None)] for every graph of the run"""
    list_file = os.path.join(args.dir, "graphs.txt")
    if not os.path.exists(list_file):
        sys.exit(f"No run in {args.dir} (cluster/find_k.py submit first, or give --tag)")
    with open(list_file) as f:
        graphs = f.read().split()
    return [(g, read_json(result_path(args.dir, i, g))) for i, g in enumerate(graphs, 1)]


def better(new, old):
    """Whether result new improves on the project file's entry old"""
    if not isinstance(old, dict) or old.get("k") is None:
        return True  # no entry, a bare integer from an old file, or skipped as too large
    if old.get("status") == "OPTIMAL":
        return False
    return new["status"] == "OPTIMAL" or new["k"] < old["k"]


def status(args):
    results = collect(args)
    counts = {"OPTIMAL": 0, "FEASIBLE": 0, "not started or failed": 0}
    for _, r in results:
        counts[r["status"] if r else "not started or failed"] += 1
    print(f"{len(results)} graphs in {args.dir}: " + ", ".join(f"{n} {s}" for s, n in counts.items()))
    print("Graphs still running show as FEASIBLE until they finish (see squeue -u $USER).")


def merge(args):
    known = load_k_file()
    merged = dict(known)
    improved = []
    for graph, r in collect(args):
        if not r:
            continue
        entry = {k: r[k] for k in ("k", "status", "source", "proof", "clique", "solver", "timeout") if k in r}
        old = known.get(graph)
        if better(entry, old):
            merged[graph] = entry
            was = f"K={old['k']} {old['status']}" if isinstance(old, dict) and old.get("k") else "no K"
            improved.append(f"  {graph}: {was} -> K={entry['k']} {entry['status']}")
        elif isinstance(old, dict) and old.get("status") == "OPTIMAL" and entry["k"] < old["k"]:
            print(f"Warning: {graph} was OPTIMAL at K={old['k']} but a {entry['k']}-coloring was found; kept the old entry")
    if args.in_place:
        backup = os.path.join(PROJECT, f"optimal_k_values_backup_{int(time.time())}.json")
        shutil.copy(K_FILE, backup)
        target = K_FILE
        print(f"Backed up the previous file to {backup}")
    else:
        target = os.path.join(args.dir, "optimal_k_values.json")
    fok.save(merged, target)
    statuses = [v.get("status") if isinstance(v, dict) else None for v in merged.values()]
    print("\n".join(improved) if improved else "No graph improved.")
    print(f"\nWrote {target}: {len(merged)} graphs, {statuses.count('OPTIMAL')} OPTIMAL "
          f"(was {sum(1 for v in known.values() if isinstance(v, dict) and v.get('status') == 'OPTIMAL')}), "
          f"{statuses.count('FEASIBLE')} FEASIBLE, {len(improved)} improved")


if __name__ == "__main__":
    a = parse_args()
    {"submit": submit, "task": run_task, "status": status, "merge": merge}[a.command](a)
