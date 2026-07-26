import subprocess
import time
import os

SOTA_BIN = "/root/coloringsolver/install/bin/coloringsolver"
SMT_BASIC_BIN = "./build/smt_test"
SMT_SYM_BIN = "./build/smt_solver_sym"

# Hardcoded optimal/target K values for the specific DIMACS benchmarks
TARGET_K = {
    "DSJC125.1.col": 6,
    "DSJC250.1.col": 10
}

def run_sota(graph_path):
    start = time.time()
    cmd = [SOTA_BIN, "--input", graph_path, "--algorithm", "greedy-dsatur"]
    result = subprocess.run(cmd, capture_output=True, text=True)
    duration = time.time() - start
    
    # Extract K from SOTA output (assuming standard DIMACS output format 's col <K>')
    k_val = "N/A"
    for line in result.stdout.split('\n'):
        if line.startswith("s col"):
            k_val = line.split()[2]
            break
    return k_val, duration

def run_smt(binary_path, graph_path, k):
    start = time.time()
    cmd = [binary_path, graph_path, str(k)]
    # Run with a timeout just in case it hangs
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        duration = time.time() - start
        
        status = "UNKNOWN"
        if "SAT" in result.stdout and "UNSAT" not in result.stdout:
            status = "SAT"
        elif "UNSAT" in result.stdout:
            status = "UNSAT"
            
        return status, duration
    except subprocess.TimeoutExpired:
        return "TIMEOUT", 120.0

def main():
    benchmarks = ["benchmarks/DSJC125.1.col", "benchmarks/DSJC250.1.col"]
    
    print(f"{'Graph':<15} | {'K':<4} | {'SOTA Time':<10} | {'Basic SMT':<12} | {'Sym SMT':<12}")
    print("-" * 65)
    
    for graph in benchmarks:
        if not os.path.exists(graph):
            continue
            
        filename = os.path.basename(graph)
        k = TARGET_K.get(filename, 10)
        
        # 1. Run SOTA
        sota_k, sota_time = run_sota(graph)
        
        # 2. Run Basic SMT
        basic_res, basic_time = run_smt(SMT_BASIC_BIN, graph, k)
        
        # 3. Run Symmetry Breaking SMT
        sym_res, sym_time = run_smt(SMT_SYM_BIN, graph, k)
        
        print(f"{filename:<15} | {k:<4} | {sota_time:<8.4f} s | {basic_time:<8.4f} s | {sym_time:<8.4f} s")

if __name__ == "__main__":
    main()