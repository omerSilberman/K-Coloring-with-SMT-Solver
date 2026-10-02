import time
import subprocess
import os
import sys
import argparse
import json
import ast
from datetime import datetime

try:
    import networkx as nx
except ImportError:
    print("Error: Missing networkx library. Please run: pip3 install networkx")
    sys.exit(1)

try:
    from ortools.sat.python import cp_model
except ImportError:
    print("Error: Missing ortools library. Please run: pip3 install ortools")
    sys.exit(1)

SOTA_BIN = "/root/coloringsolver/install/bin/coloringsolver"
LIB_PATH = "/usr/local/lib"
DEFAULT_TIMEOUT = 20.0

class DualLogger:
    def __init__(self, filepath):
        self.terminal = sys.stdout
        self.log = open(filepath, "w")

    def write(self, message):
        self.terminal.write(message)
        self.log.write(message)

    def flush(self):
        self.terminal.flush()
        self.log.flush()

def get_graph_stats(graph_path):
    """Parses node count and edge count from DIMACS file."""
    num_nodes = 0
    num_edges = 0
    with open(graph_path, 'r') as f:
        for line in f:
            if line.startswith('p '):
                parts = line.split()
                num_nodes = int(parts[2])
                if len(parts) > 3 and parts[3].isdigit():
                    num_edges = int(parts[3])
                    return num_nodes, num_edges
            elif line.startswith('e '):
                num_edges += 1
    return num_nodes, num_edges

def generate_small_benchmarks():
    os.makedirs("benchmarks", exist_ok=True)
    graphs = {
        "myciel3.col": nx.mycielski_graph(3),
        "myciel4.col": nx.mycielski_graph(4),
        "myciel5.col": nx.mycielski_graph(5)
    }
    for filename, G in graphs.items():
        filepath = os.path.join("benchmarks", filename)
        if not os.path.exists(filepath):
            with open(filepath, 'w') as f:
                f.write(f"p edge {G.number_of_nodes()} {G.number_of_edges()}\n")
                for u, v in G.edges():
                    f.write(f"e {u+1} {v+1}\n")

def run_sota_solver(graph_path):
    start = time.time()
    cmd = [SOTA_BIN, "--input", graph_path, "--algorithm", "greedy-dsatur"]
    result = subprocess.run(cmd, capture_output=True, text=True)
    duration = time.time() - start
    
    k_val = "N/A"
    full_output = result.stdout + "\n" + result.stderr 
    
    for line in full_output.split('\n'):
        line = line.strip()
        if line.startswith("Number of colors:"):
            k_val = line.split(":")[1].strip()
            break
            
    return k_val, duration

def run_academic_solver(binary_path, graph_path, k, produce_model, timeout):
    start = time.time()
    cmd = [binary_path, "--bound", str(k), graph_path]
    
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        duration = time.time() - start
        
        status, model_str = "UNKNOWN", ""
        full_output = result.stdout + "\n" + result.stderr
        
        if "PARSE ERROR" in full_output:
            return "ERROR", duration, ""
            
        for line in full_output.split('\n'):
            line = line.strip().lower()
            words = line.replace(":", " ").replace(",", " ").split()
            
            if "unsat" in words or "unfeasible" in words:
                status = "UNSAT"
            elif "optimal" in words or "optimum" in words or "sat" in words or ("colors" in words and "number" in words):
                status = "SAT"
                
        if status == "UNKNOWN" and result.returncode == 0:
            return "UNKNOWN", duration, ""
            
        return status, duration, model_str
    except subprocess.TimeoutExpired:
        return "TIMEOUT", timeout, ""

def run_smt(binary_path, graph_path, k, produce_model, timeout):
    start = time.time()
    
    if isinstance(binary_path, list):
        cmd = binary_path + [graph_path, str(k)]
    else:
        cmd = [binary_path, graph_path, str(k)]
        
    if produce_model:
        cmd.append("--model")
        
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = LIB_PATH
        
    try:
        result = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=timeout)
        duration = time.time() - start
        
        status, model_str = "UNKNOWN", ""
        for line in result.stdout.split('\n'):
            if "SAT" in line and "UNSAT" not in line:
                status = "SAT"
            elif "UNSAT" in line:
                status = "UNSAT"
            elif line.startswith("MODEL:"):
                model_str = line.replace("MODEL:", "").strip()
                
        return status, duration, model_str
    except subprocess.TimeoutExpired:
        return "TIMEOUT", timeout, ""

def run_ortools(graph_path, k, produce_model, timeout):
    start = time.time()
    
    edges = []
    num_nodes = 0
    with open(graph_path, 'r') as f:
        for line in f:
            if line.startswith('p '):
                num_nodes = int(line.split()[2])
            elif line.startswith('e '):
                parts = line.split()
                edges.append((int(parts[1]), int(parts[2])))
                
    model = cp_model.CpModel()
    colors = {i: model.NewIntVar(0, k - 1, f'c_{i}') for i in range(1, num_nodes + 1)}
    
    for u, v in edges:
        model.Add(colors[u] != colors[v])
        
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = timeout
    
    status_code = solver.Solve(model)
    duration = time.time() - start
    
    model_str = ""
    if status_code in [cp_model.OPTIMAL, cp_model.FEASIBLE]:
        status = "SAT"
        if produce_model:
            model_str = " ".join([str(solver.Value(colors[i])) for i in range(1, num_nodes + 1)])
    elif status_code == cp_model.INFEASIBLE:
        status = "UNSAT"
    else:
        status = "TIMEOUT"
        duration = timeout
        
    return status, duration, model_str

def main():
    parser = argparse.ArgumentParser(description="Graph Coloring Benchmark")
    parser.add_argument("--model", action="store_true", help="Produce and print coloring models")
    parser.add_argument("--json", type=str, default="optimal_k_values.json", help="Path to the JSON file containing K values")
    parser.add_argument("--solvers", type=str, default="solvers_switch.conf", help="Path to the solvers configuration file")
    parser.add_argument("--input-list", type=str, help="Text file with a specific list of graph paths to test (one per line)")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT, help="Timeout in seconds per solver per graph (default: 20.0)")
    args = parser.parse_args()
    
    if not os.path.exists(args.json):
        print(f"Error: JSON file '{args.json}' not found.")
        sys.exit(1)
        
    if not os.path.exists(args.solvers):
        print(f"Error: Solvers config file '{args.solvers}' not found.")
        sys.exit(1)
        
    # Load Solvers Configuration safely using AST
    with open(args.solvers, 'r') as f:
        try:
            SMT_SOLVERS = ast.literal_eval(f.read())
        except Exception as e:
            print(f"Error parsing solvers config file '{args.solvers}': {e}")
            sys.exit(1)
        
    with open(args.json, 'r') as f:
        k_data = json.load(f)
        
    target_graphs = {}
    for path, data in k_data.items():
        k = None
        if isinstance(data, int):
            k = data
        elif isinstance(data, dict):
            k = data.get("k")
            
        if k is not None:
            target_graphs[path] = k
            
    if args.input_list:
        if not os.path.exists(args.input_list):
            print(f"Error: Input list file '{args.input_list}' not found.")
            sys.exit(1)
            
        with open(args.input_list, 'r') as f:
            allowed_keys = {line.strip() for line in f if line.strip()}
            
        target_graphs = {p: k for p, k in target_graphs.items() if p in allowed_keys}

    if not target_graphs:
        print("No valid graphs to benchmark. Exiting.")
        sys.exit(0)

    os.makedirs("logs", exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_filename = os.path.join("logs", f"benchmark_results_{timestamp}.txt")
    sys.stdout = DualLogger(log_filename)
    
    print("--- Starting Benchmark Run ---")
    print(f"Logs are automatically being saved to: {log_filename}")
    print(f"Using Solvers Config: {args.solvers}")
    print(f"Total Valid Graphs to test: {len(target_graphs)}")
    print(f"Timeout per solver: {args.timeout:.1f}s\n")
    
    generate_small_benchmarks()
    
    results_models = []
    
    # Table Header with Nodes and Edges columns
    header = f"{'Graph':<22} | {'Nodes':<6} | {'Edges':<8} | {'K':<4} | {'SOTA Time':<10} | {'SOTA K':<8}"
    for solver in SMT_SOLVERS:
        header += f" | {solver['name']:<10}"
        
    print(header)
    print("-" * len(header))
    
    total_tested = 0
    nodes_list = []
    edges_list = []
    target_k_list = []
    sota_times = []
    sota_k_list = []
    solver_runtimes = {solver['name']: [] for solver in SMT_SOLVERS}
    solver_solved = {solver['name']: 0 for solver in SMT_SOLVERS}
    
    for graph_path, k in target_graphs.items():
        if not os.path.exists(graph_path):
            continue
            
        filename = os.path.basename(graph_path)
        nodes, edges = get_graph_stats(graph_path)
        
        s_k, s_t = run_sota_solver(graph_path)
        s_t_str = f"{s_t:.4f}s"
        
        total_tested += 1
        nodes_list.append(nodes)
        edges_list.append(edges)
        target_k_list.append(k)
        sota_times.append(s_t)
        if s_k.isdigit():
            sota_k_list.append(int(s_k))
        
        # Live-stream prefix with Graph, Nodes, Edges, K, and SOTA stats
        row_prefix = f"{filename:<22} | {nodes:<6} | {edges:<8} | {k:<4} | {s_t_str:<10} | {s_k:<8}"
        print(row_prefix, end="", flush=True)
        
        graph_models = {}
        
        for solver in SMT_SOLVERS:
            if solver['name'] == "GC-CDCL":
                res, runtime, model_str = run_academic_solver(solver['bin_path'], graph_path, k, args.model, args.timeout)
            elif solver['name'] == "OR-Tools":
                res, runtime, model_str = run_ortools(graph_path, k, args.model, args.timeout)
            else:
                res, runtime, model_str = run_smt(solver['bin_path'], graph_path, k, args.model, args.timeout)
                
            solver_runtimes[solver['name']].append(runtime)
            if res == "SAT":
                solver_solved[solver['name']] += 1

            if res in ["TIMEOUT", "ERROR"]:
                time_str = res
            else:
                time_str = f"{res[:3]} {runtime:.3f}s"
                
            print(f" | {time_str:<10}", end="", flush=True)
            
            if args.model:
                graph_models[solver['name']] = model_str
                
        print() 
        
        if args.model:
            results_models.append({
                "graph": filename, 
                "k": k, 
                "models": graph_models
            })

    # Summary Statistics
    if total_tested > 0:
        print("-" * len(header))
        
        avg_nodes = sum(nodes_list) / total_tested
        avg_edges = sum(edges_list) / total_tested
        avg_target_k = sum(target_k_list) / total_tested
        avg_sota_t = sum(sota_times) / total_tested
        avg_sota_k_str = f"{sum(sota_k_list) / len(sota_k_list):.1f}" if sota_k_list else "N/A"
        
        avg_row_str = f"{'AVERAGE':<22} | {f'{avg_nodes:.1f}':<6} | {f'{avg_edges:.1f}':<8} | {f'{avg_target_k:.1f}':<4} | {f'{avg_sota_t:.4f}s':<10} | {avg_sota_k_str:<8}"
        for solver in SMT_SOLVERS:
            runtimes = solver_runtimes[solver['name']]
            avg_r = sum(runtimes) / len(runtimes) if runtimes else 0.0
            avg_row_str += f" | {f'{avg_r:.3f}s':<10}"
        print(avg_row_str)
        
        solved_row_str = f"{'SOLVED / TOTAL':<22} | {'-':<6} | {'-':<8} | {'-':<4} | {'-':<10} | {'-':<8}"
        for solver in SMT_SOLVERS:
            solved_count = solver_solved[solver['name']]
            solved_row_str += f" | {f'{solved_count}/{total_tested}':<10}"
        print(solved_row_str)

    if args.model and results_models:
        print("\n" + "=" * len(header))
        print("GENERATED MODELS (Node 1 -> Node N)")
        print("=" * len(header))
        for rm in results_models:
            print(f"\n--- {rm['graph']} (Target K={rm['k']}) ---")
            for solver in SMT_SOLVERS:
                prefix = solver['model_prefix']
                model_out = rm['models'].get(solver['name'], "")
                print(f"{prefix:<10}: {model_out}")

    print("\n--- Benchmark Complete ---")

if __name__ == "__main__":
    main()