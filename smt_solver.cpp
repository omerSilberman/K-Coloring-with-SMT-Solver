#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include "smt-switch/cvc5_factory.h"
#include "smt-switch/smt.h"

using namespace std;

// Structure to hold our graph edges
struct Edge {
    int u;
    int v;
};

int main(int argc, char** argv) {
    // 1. Handle command line arguments
    if (argc < 3) {
        cerr << "Usage: " << argv[0] << " <graph.col> <K>" << endl;
        return 1;
    }
    
    string filename = argv[1];
    int K = stoi(argv[2]);

    // Check if user requested model generation
    bool produce_model = (argc >= 4 && string(argv[3]) == "--model");

    int num_nodes = 0;
    int num_edges = 0;
    vector<Edge> edges;

    // 2. Parse the DIMACS (.col) file
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "Error: Could not open file " << filename << endl;
        return 1;
    }

    string line;
    while (getline(file, line)) {
        if (line.empty() || line[0] == 'c') continue; // Skip comments
        
        stringstream ss(line);
        string type;
        ss >> type;
        
        if (type == "p") {
            string format;
            ss >> format >> num_nodes >> num_edges;
        } else if (type == "e") {
            int u, v;
            ss >> u >> v;
            edges.push_back({u, v});
        }
    }
    file.close();

    cout << "c Parsed graph with " << num_nodes << " nodes and " << edges.size() << " edges." << endl;
    cout << "c Searching for a " << K << "-coloring..." << endl;

    try {
        // 3. Initialize the SMT solver with QF_LIA (Linear Integer Arithmetic)
        smt::SmtSolver solver = smt::Cvc5SolverFactory::create(false);
        // Enable model production inside cvc5 if flag is set
        if (produce_model) {
            solver->set_opt("produce-models", "true");
        }
        solver->set_logic("QF_LIA");
        
        // Define the Integer sort (type)
        smt::Sort int_sort = solver->make_sort(smt::INT);
        
        // Create SMT constants for 1 and K
        smt::Term one = solver->make_term("1", int_sort);
        smt::Term k_term = solver->make_term(to_string(K), int_sort);

        // Vector to hold our node variables (1-indexed to match DIMACS)
        vector<smt::Term> node_vars(num_nodes + 1);

        // 4. Create variables and domain constraints: 1 <= color <= K
        for (int i = 1; i <= num_nodes; ++i) {
            // Create integer variable for the node
            node_vars[i] = solver->make_symbol("node_" + to_string(i), int_sort);
            
            // Constraint: node >= 1
            smt::Term ge_one = solver->make_term(smt::Ge, node_vars[i], one);
            solver->assert_formula(ge_one);
            
            // Constraint: node <= K
            smt::Term le_k = solver->make_term(smt::Le, node_vars[i], k_term);
            solver->assert_formula(le_k);
        }

        // 5. Create edge constraints: color(u) != color(v)
        for (const auto& edge : edges) {
            // formula: Not(Equal(u, v))
            smt::Term u_eq_v = solver->make_term(smt::Equal, node_vars[edge.u], node_vars[edge.v]);
            smt::Term u_neq_v = solver->make_term(smt::Not, u_eq_v);
            solver->assert_formula(u_neq_v);
        }

        // 6. Check Satisfiability
        smt::Result res = solver->check_sat();

        // 7. Output Results
        if (res.is_sat()) {
            cout << "s sat" << endl;
            cout << "s col " << K << endl;
            
            if (produce_model) {
            cout << "MODEL: ";
            for (int i = 1; i <= num_nodes; i++) {
                cout << solver->get_value(node_vars[i])->to_string() << " ";
            }
            cout << endl;
        }
        } else if (res.is_unsat()) {
            cout << "s unsat" << endl;
        } else {
            cout << "s unknown" << endl;
        }

    } catch (const exception& e) {
        cerr << "Exception caught: " << e.what() << endl;
        return 1;
    }

    return 0;
}