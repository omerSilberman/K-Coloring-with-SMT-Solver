import os
import glob
import json
import time
import sys
import shutil
import subprocess
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

def get_greedy_upper_bound(num_nodes, edges):
    adj = {i: [] for i in range(1, num_nodes + 1)}
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        
    colors = {}
    for node in range(1, num_nodes + 1):
        neighbor_colors = {colors[neighbor] for neighbor in adj[node] if neighbor in colors}
        c = 1
        while c in neighbor_colors:
            c += 1
        colors[node] = c
    return max(colors.values()) if colors else 1

# =============================================================================
# 2. SOLVER ROUTINES
# =============================================================================
def solve_with_ortools(num_nodes, edges, timeout_sec=20.0):
    model = cp_model.CpModel()
    max_color = model.NewIntVar(1, num_nodes, 'max_color')
    
    node_colors = {}
    for i in range(1, num_nodes + 1):
        node_colors[i] = model.NewIntVar(1, num_nodes, f'node_{i}')
        model.Add(node_colors[i] <= max_color)
        
    for u, v in edges:
        model.Add(node_colors[u] != node_colors[v])
        
    model.Minimize(max_color)
    
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = timeout_sec
    
    status = solver.Solve(model)
    if status == cp_model.OPTIMAL:
        return int(solver.ObjectiveValue()), "OPTIMAL"
    elif status == cp_model.FEASIBLE:
        return int(solver.ObjectiveValue()), "FEASIBLE (TIMEOUT BOUND)"
    return None, "TIMEOUT/ERROR"

def solve_with_smt_binary(filepath, binary_path, theory, upper_bound):
    current_k = upper_bound
    optimal_k = current_k
    
    while current_k > 0:
        print(f"      -> Testing K={current_k - 1}...", end=" ", flush=True)
        cmd = [binary_path, theory, filepath, str(current_k - 1)]
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
            output = result.stdout
            
            if "UNSAT" in output:
                print("UNSAT! Found optimal.")
                return optimal_k, "OPTIMAL"
            elif "SAT" in output:
                print("SAT!")
                current_k -= 1
                optimal_k = current_k
            else:
                print("CRASH/UNKNOWN.")
                break
        except subprocess.TimeoutExpired:
            print("TIMEOUT.")
            break
            
    return optimal_k, "FEASIBLE (TIMEOUT BOUND)"

# =============================================================================
# 3. MAIN RUNNER WITH RESUME & MIGRATION
# =============================================================================
def run_discovery(benchmark_dir="benchmarks", solver_mode="OR-TOOLS", fresh_start=False):
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

    print(f"--- Starting Discovery on {total_files} files (Mode: {solver_mode}) ---\n")

    for index, filepath in enumerate(files, 1):
        rel_path = Path(filepath).as_posix()
        filename = Path(filepath).name
        
        # Check if already processed (supports both relative path and old filename keys)
        if rel_path in optimal_k_dict:
            continue
        elif filename in optimal_k_dict:
            # Migrate old filename entry to relative path without recomputing
            optimal_k_dict[rel_path] = optimal_k_dict.pop(filename)
            with open(output_file, 'w') as f:
                json.dump(optimal_k_dict, f, indent=4)
            continue

        print(f"[{index}/{total_files}] Processing: {rel_path}")
        num_nodes, edges = parse_dimacs(filepath)
        
        # --- ADD THIS SAFEGUARD ---
        # If a graph has more than 20,000 edges, it will crash WSL. Skip it safely.
        if len(edges) > 20000:
            print(f"   => SKIPPED: Graph is too massive ({len(edges)} edges) and will crash WSL.\n")
            optimal_k_dict[rel_path] = {"k": None, "status": "SKIPPED_TOO_LARGE"}
            with open(output_file, 'w') as f:
                json.dump(optimal_k_dict, f, indent=4)
            continue
        # --------------------------

        start_time = time.time()
        
        if solver_mode == "OR-TOOLS" and HAS_ORTOOLS:
            opt_k, status_label = solve_with_ortools(num_nodes, edges)
        else:
            greedy_k = get_greedy_upper_bound(num_nodes, edges)
            opt_k, status_label = solve_with_smt_binary(filepath, "./build/smt_solver", solver_mode, greedy_k)
            
        elapsed = time.time() - start_time
        
        if opt_k is not None:
            print(f"   => K: {opt_k} [{status_label}] (Elapsed: {elapsed:.2f}s)\n")
            optimal_k_dict[rel_path] = opt_k
            
            with open(output_file, 'w') as f:
                json.dump(optimal_k_dict, f, indent=4)
        else:
            print(f"   => FAILED to find valid K within timeout.\n")

if __name__ == "__main__":
    is_fresh = "--fresh" in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    
    mode = args[0] if len(args) > 0 else "OR-TOOLS"
    target_dir = args[1] if len(args) > 1 else "benchmarks"
    
    run_discovery(benchmark_dir=target_dir, solver_mode=mode, fresh_start=is_fresh)