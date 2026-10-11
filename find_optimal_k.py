import os
import argparse
import glob
import json
import time
import sys
import shutil
import subprocess
import heapq
import re
from pathlib import Path

try:
    from ortools.sat.python import cp_model
    HAS_ORTOOLS = True
except ImportError:
    HAS_ORTOOLS = False
    print("Warning: Google OR-Tools not installed. Run 'pip install ortools'.")

# =============================================================================
# 1. GRAPH PARSING & HEURISTICS
# =============================================================================
def parse_dimacs(filepath):
    num_nodes = 0
    edges = []
    with open(filepath, 'r') as f:
        for line in f:
            if line.startswith('p'):
                parts = line.split()
                num_nodes = int(parts[2])
            elif line.startswith('e'):
                parts = line.split()
                edges.append((int(parts[1]), int(parts[2])))
    return num_nodes, edges

def build_adjacency(num_nodes, edges):
    adj = [set() for _ in range(num_nodes + 1)]
    for u, v in edges:
        if u != v:
            adj[u].add(v)
            adj[v].add(u)
    return adj

def dsatur_upper_bound(num_nodes, adj):
    """Number of colors used by DSATUR (Brelaz 1979): always color next the node whose
    neighbors already use the most distinct colors (ties: highest degree), giving it the
    smallest free color. The result is a real coloring, so it is a feasible K."""
    color = [0] * (num_nodes + 1)
    neighbor_colors = [set() for _ in range(num_nodes + 1)]
    heap = [(0, -len(adj[v]), v) for v in range(1, num_nodes + 1)]
    heapq.heapify(heap)
    used = 0
    while heap:
        saturation, _, v = heapq.heappop(heap)
        if color[v] or -saturation != len(neighbor_colors[v]):
            continue  # already colored, or a stale heap entry
        c = 1
        while c in neighbor_colors[v]:
            c += 1
        color[v] = c
        used = max(used, c)
        for u in adj[v]:
            if not color[u] and c not in neighbor_colors[u]:
                neighbor_colors[u].add(c)
                heapq.heappush(heap, (-len(neighbor_colors[u]), -len(adj[u]), u))
    return max(used, 1)

def greedy_clique_lower_bound(num_nodes, adj, starts=50):
    """Size of a clique (nodes all adjacent to each other) found greedily. A clique of size c
    needs c different colors, so c is a lower bound on K. Grows a clique from each of the
    `starts` highest-degree nodes, always adding the candidate (a node adjacent to the whole
    clique so far) with the most neighbors among the other candidates."""
    if num_nodes == 0:
        return 0
    best = 1
    by_degree = sorted(range(1, num_nodes + 1), key=lambda v: -len(adj[v]))
    for start in by_degree[:starts]:
        size, candidates = 1, set(adj[start])
        while candidates:
            if len(candidates) <= 300:
                v = max(candidates, key=lambda u: len(adj[u] & candidates))
            else:
                v = max(candidates, key=lambda u: len(adj[u]))  # cheaper for big candidate sets
            size += 1
            candidates &= adj[v]
        best = max(best, size)
    return best

# =============================================================================
# 2. SOLVER ROUTINES
# =============================================================================
# Every solver returns (k, status, source, proof):
#   status  "OPTIMAL"  - k colors work and k-1 was proven impossible
#           "FEASIBLE" - k colors work (an actual coloring was found), but k-1 is unresolved
#   source  what produced the k-coloring: "DSATUR", "SAT" (the SMT solver), "OR-TOOLS",
#           or "previous run" when an earlier result could not be improved
#   proof   for OPTIMAL, how k-1 was ruled out: "UNSAT" (SMT solver), "OR-TOOLS",
#           or "clique" (the graph has a clique of size k, so fewer colors are impossible)
# Both solvers start from a known k-coloring (known_k) and never search below the
# clique lower bound.
def solve_with_ortools(num_nodes, edges, timeout_sec, known_k, known_source, clique):
    upper = known_k - 1
    model = cp_model.CpModel()
    max_color = model.NewIntVar(clique, upper, 'max_color')

    node_colors = {}
    for i in range(1, num_nodes + 1):
        node_colors[i] = model.NewIntVar(1, upper, f'node_{i}')
        model.Add(node_colors[i] <= max_color)

    for u, v in edges:
        model.Add(node_colors[u] != node_colors[v])

    model.Minimize(max_color)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = timeout_sec

    status = solver.Solve(model)
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        k = int(solver.ObjectiveValue())
        if k == clique:
            return k, "OPTIMAL", "OR-TOOLS", "clique"
        if status == cp_model.OPTIMAL:
            return k, "OPTIMAL", "OR-TOOLS", "OR-TOOLS"
        return k, "FEASIBLE", "OR-TOOLS", None
    elif status == cp_model.INFEASIBLE:
        # Nothing below known_k exists, so known_k is optimal
        return known_k, "OPTIMAL", known_source, "OR-TOOLS"
    return known_k, "FEASIBLE", known_source, None

def colors_in_model(output):
    """Number of distinct colors in a `MODEL: node_1: v node_2: v ...` line (other
    variables printed after the nodes, like the array encodings' indices, are ignored)."""
    line = next((l for l in output.splitlines() if l.startswith("MODEL:")), None)
    if line is None:
        return None
    parts = re.split(r"(?:^|\s)([A-Za-z]\w*): ", line[len("MODEL:"):])
    values = {parts[i + 1].strip() for i in range(1, len(parts) - 1, 2) if re.fullmatch(r"node_\d+", parts[i])}
    return len(values) or None

def solve_with_smt_binary(filepath, binary_path, theory, known_k, known_source, timeout_sec, clique):
    # known_k colors are known to work; ask for k-1 colors until UNSAT. When the solver finds a
    # coloring, it may use fewer than k-1 colors, so jump straight to the number it used.
    best_k, source = known_k, known_source

    while best_k > clique:
        print(f"      -> Testing K={best_k - 1}...", end=" ", flush=True)
        cmd = [binary_path, theory, filepath, str(best_k - 1), "--model"]

        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_sec)
            output = result.stdout

            if "UNSAT" in output:
                print("UNSAT! Found optimal.")
                return best_k, "OPTIMAL", source, "UNSAT"
            elif "SAT" in output:
                used = min(colors_in_model(output) or best_k - 1, best_k - 1)
                print(f"SAT! (the coloring uses only {used} colors)" if used < best_k - 1 else "SAT!")
                best_k, source = used, "SAT"
            else:
                print("CRASH/UNKNOWN.")
                break
        except subprocess.TimeoutExpired:
            print("TIMEOUT.")
            break
    else:
        # best_k reached the clique size, so fewer colors are impossible
        return best_k, "OPTIMAL", source, "clique"

    return best_k, "FEASIBLE", source, None

# =============================================================================
# 3. MAIN RUNNER WITH RESUME & MIGRATION
# =============================================================================
EDGE_LIMIT = 200000

def save(optimal_k_dict, output_file):
    with open(output_file, 'w') as f:
        json.dump(optimal_k_dict, f, indent=4)

def previous_result(entry):
    """What an earlier run left for a graph: (k, status, source).
    Old files stored a bare integer; that k came from a real coloring,
    but whether it is optimal is unknown, so it is treated as FEASIBLE."""
    if isinstance(entry, int):
        return entry, "FEASIBLE", "previous run"
    return entry.get("k"), entry.get("status"), entry.get("source", "previous run")

def run_discovery(benchmark_dir="benchmarks", solver_mode="OR-TOOLS", fresh_start=False, timeout_sec=None):
    files = []
    for ext in ('*.col', '*.clq'):
        files.extend(glob.glob(os.path.join(benchmark_dir, '**', ext), recursive=True))
    
    files = sorted(files)
    total_files = len(files)
    output_file = "optimal_k_values.json"
    optimal_k_dict = {}

    if fresh_start and os.path.exists(output_file):
        backup_name = f"optimal_k_values_backup_{int(time.time())}.json"
        shutil.copy(output_file, backup_name)
        print(f"Backed up existing results to {backup_name}")
        optimal_k_dict = {}
    elif os.path.exists(output_file):
        with open(output_file, 'r') as f:
            optimal_k_dict = json.load(f)
        print(f"Loaded existing file with {len(optimal_k_dict)} entries. Checking resume progress...")

    use_ortools = solver_mode == "OR-TOOLS" and HAS_ORTOOLS
    if timeout_sec is None:
        timeout_sec = 20.0 if use_ortools else 60.0
    print(f"--- Starting Discovery on {total_files} files (Mode: {solver_mode}, timeout: {timeout_sec:g}s"
          f"{' per call' if not use_ortools else ''}) ---\n")

    for index, filepath in enumerate(files, 1):
        rel_path = Path(filepath).as_posix()
        filename = Path(filepath).name

        # Migrate old filename keys to relative path keys
        if rel_path not in optimal_k_dict and filename in optimal_k_dict:
            optimal_k_dict[rel_path] = optimal_k_dict.pop(filename)
            save(optimal_k_dict, output_file)

        # Resume: skip proven optima, retry FEASIBLE results starting below their k,
        # and reconsider graphs skipped for size (the limit may have been raised)
        known_k, known_source = None, None
        if rel_path in optimal_k_dict:
            prev_k, prev_status, prev_source = previous_result(optimal_k_dict[rel_path])
            if prev_status == "OPTIMAL":
                continue
            if prev_status == "FEASIBLE" and prev_k is not None:
                known_k, known_source = prev_k, prev_source

        num_nodes, edges = parse_dimacs(filepath)
        print(f"[{index}/{total_files}] Processing: {rel_path} ({num_nodes} nodes, {len(edges)} edges)")

        # Very large graphs used to exhaust memory, so skip them
        if len(edges) > EDGE_LIMIT:
            print(f"   => SKIPPED: Graph is too large ({len(edges)} edges > {EDGE_LIMIT}).\n")
            optimal_k_dict[rel_path] = {"k": None, "status": "SKIPPED_TOO_LARGE"}
            save(optimal_k_dict, output_file)
            continue

        start_time = time.time()

        # Bounds: a DSATUR coloring gives a feasible K (an upper bound), a clique a lower bound
        adj = build_adjacency(num_nodes, edges)
        dsatur_k = dsatur_upper_bound(num_nodes, adj)
        clique = greedy_clique_lower_bound(num_nodes, adj)
        if known_k is not None:
            print(f"      Previous result: K={known_k} (FEASIBLE, coloring from {known_source})")
        print(f"      DSATUR coloring: {dsatur_k} colors. Largest clique found: {clique} nodes (so K >= {clique})")
        if known_k is None or dsatur_k < known_k:
            known_k, known_source = dsatur_k, "DSATUR"

        if known_k <= clique:
            opt_k, status_label, source, proof = known_k, "OPTIMAL", known_source, "clique"
        elif use_ortools:
            opt_k, status_label, source, proof = solve_with_ortools(
                num_nodes, edges, timeout_sec, known_k, known_source, clique)
        else:
            opt_k, status_label, source, proof = solve_with_smt_binary(
                filepath, "./build/smt_solver_cvc5", solver_mode, known_k, known_source, timeout_sec, clique)

        elapsed = time.time() - start_time

        if proof == "clique":
            how = f"OPTIMAL by clique: the graph has a clique of {clique} nodes"
        elif proof:
            how = f"OPTIMAL, K-1 ruled out by {proof}"
        else:
            how = "FEASIBLE"
        print(f"   => K: {opt_k} [{how}; coloring from {source}] (Elapsed: {elapsed:.2f}s)\n")
        entry = {"k": opt_k, "status": status_label, "source": source}
        if proof:
            entry["proof"] = proof
        entry.update({"clique": clique, "solver": solver_mode, "timeout": timeout_sec})
        optimal_k_dict[rel_path] = entry
        save(optimal_k_dict, output_file)

HELP_EPILOG = """
modes:
  OR-TOOLS          Minimize the number of colors with OR-Tools CP-SAT (default timeout 20 s per graph).
  <THEORY>          Any encoding of ./build/smt_solver_cvc5 (LIA, BV, BV-ZERO, FF-POLY, ...).
                    Starts from a known coloring with K colors and asks the solver for K-1 colors,
                    until UNSAT (default timeout 60 s per call). When the solver finds a coloring
                    that uses fewer colors than asked, the search jumps straight below it.

bounds (computed for every graph, in all modes):
  upper bound       a DSATUR coloring (or a previous run's result, if better)
  lower bound       a clique found greedily: c mutually adjacent nodes need c different colors.
                    When the coloring's K equals the clique size, K is optimal without any solver call.

results (optimal_k_values.json), one entry per graph:
  {"k": 6, "status": "OPTIMAL", "source": "SAT", "proof": "UNSAT", "clique": 5, "solver": "BV", "timeout": 60.0}
  status  OPTIMAL            k colors work and k-1 was proven impossible
          FEASIBLE           k colors work (a real coloring exists), but k-1 is unresolved
          SKIPPED_TOO_LARGE  more than %d edges, not attempted
  source  what produced the k-coloring: DSATUR, SAT, OR-TOOLS, or "previous run"
  proof   (OPTIMAL only) what ruled out k-1: UNSAT, OR-TOOLS, or clique
  clique  size of the clique found (a lower bound on K)

resuming (without --fresh):
  OPTIMAL graphs are skipped. FEASIBLE graphs are retried starting from k-1, so a rerun with a
  larger --timeout can turn them into OPTIMAL. Graphs skipped for size are reconsidered.
  Entries from older versions (a bare integer K) are treated as FEASIBLE.

examples:
  python3 find_optimal_k.py BV benchmarks --fresh     # start over with the BV encoding
  python3 find_optimal_k.py BV --timeout 300          # retry the FEASIBLE ones with 5 minutes per call
""" % EDGE_LIMIT

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Compute the smallest number of colors (K) for every .col/.clq graph in a directory, "
                    "and save the results to optimal_k_values.json.",
        epilog=HELP_EPILOG, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", nargs="?", default="OR-TOOLS",
                        help="OR-TOOLS (default) or a theory of smt_solver_cvc5, e.g. BV")
    parser.add_argument("benchmark_dir", nargs="?", default="benchmarks",
                        help="directory searched recursively for graphs (default: benchmarks)")
    parser.add_argument("--timeout", type=float, default=None, metavar="SECONDS",
                        help="time limit per solver call (default: 60 for SMT theories, 20 for OR-TOOLS)")
    parser.add_argument("--fresh", action="store_true",
                        help="back up optimal_k_values.json and recompute every graph from scratch")
    args = parser.parse_args()

    run_discovery(benchmark_dir=args.benchmark_dir, solver_mode=args.mode,
                  fresh_start=args.fresh, timeout_sec=args.timeout)