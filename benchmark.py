import time
import subprocess
import os
import sys
import argparse
from datetime import datetime

try:
    import networkx as nx
except ImportError:
    print("Error: Missing networkx library. Please run: pip3 install networkx")
    sys.exit(1)

SOTA_BIN = "/root/coloringsolver/install/bin/coloringsolver"
LIB_PATH = "/usr/local/lib"

# =====================================================================
# SOLVER CONFIGURATION
# To remove a solver from the benchmark, simply comment it out or delete it from this list.
# =====================================================================
SMT_SOLVERS = [
    {"name": "Basic SMT", "bin_path": "./build/smt_solver", "model_prefix": "C++ Basic"},
    {"name": "Sym SMT", "bin_path": "./build/smt_solver_sym", "model_prefix": "C++ Sym"},
    {"name": "BV SMT", "bin_path": "./build/smt_solver_bv", "model_prefix": "C++ BV"}
]

TARGET_K = {
    "myciel3.col": 4,   # 11 nodes
    "myciel4.col": 5,   # 23 nodes
    "myciel5.col": 6,   # 47 nodes
    "DSJC125.1.col": 6,
    "DSJC250.1.col": 8
}

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
            # Splits "Number of colors:     3" at the ":" and grabs the "3"
            k_val = line.split(":")[1].strip()
            break
            
    return k_val, duration

def run_smt(binary_path, graph_path, k, produce_model):
    start = time.time()
    cmd = [binary_path, graph_path, str(k)]
    
    if produce_model:
        cmd.append("--model")
        
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = LIB_PATH
        
    try:
        result = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=120)
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
        return "TIMEOUT", 120.0, ""

def main():
    parser = argparse.ArgumentParser(description="Graph Coloring Benchmark")
    parser.add_argument("--model", action="store_true", help="Produce and print coloring models")
    args = parser.parse_args()
    
    os.makedirs("logs", exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_filename = os.path.join("logs", f"benchmark_results_{timestamp}.txt")
    sys.stdout = DualLogger(log_filename)
    
    print("--- Starting Benchmark Run ---")
    print(f"Logs are automatically being saved to: {log_filename}\n")
    
    generate_small_benchmarks()
    
    benchmarks = ["benchmarks/" + f for f in TARGET_K.keys()]
    results_models = []
    
    # Dynamically build the table header based on the SMT_SOLVERS array
    header = f"{'Graph':<15} | {'K':<4} | {'SOTA Time':<10} | {'SOTA K':<8}"
    for solver in SMT_SOLVERS:
        header += f" | {solver['name']:<10}"
        
    print(header)
    print("-" * len(header))
    
    for graph in benchmarks:
        if not os.path.exists(graph):
            continue
            
        filename = os.path.basename(graph)
        k = TARGET_K[filename]
        
        s_k, s_t = run_sota_solver(graph)
        s_t_str = f"{s_t:.4f}s"
        
        # Start building the row string with the standard columns
        row_str = f"{filename:<15} | {k:<4} | {s_t_str:<10} | {s_k:<8}"
        
        graph_models = {}
        
        # Dynamically run each solver in the array and append its results to the row
        for solver in SMT_SOLVERS:
            res, runtime, model_str = run_smt(solver['bin_path'], graph, k, args.model)
            time_str = f"{runtime:.4f}s" if res != "TIMEOUT" else "TIMEOUT"
            row_str += f" | {time_str:<10}"
            
            if args.model:
                graph_models[solver['name']] = model_str
                
        print(row_str)
        
        if args.model:
            results_models.append({
                "graph": filename, 
                "k": k, 
                "models": graph_models
            })

    if args.model and results_models:
        print("\n" + "=" * len(header))
        print("GENERATED MODELS (Node 1 -> Node N)")
        print("=" * len(header))
        for rm in results_models:
            print(f"\n--- {rm['graph']} (Target K={rm['k']}) ---")
            # Dynamically print the model for each solver that was active
            for solver in SMT_SOLVERS:
                prefix = solver['model_prefix']
                model_out = rm['models'].get(solver['name'], "")
                print(f"{prefix:<10}: {model_out}")

    print("\n--- Benchmark Complete ---")

if __name__ == "__main__":
    main()