#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include "smt-switch/cvc5_factory.h"
#include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main(int argc, char** argv) {
    if (argc < 3) {
        cerr << "Usage: ./smt_solver_sym <dimacs_file> <K>" << endl;
        return 1;
    }

    string filename = argv[1];
    int K = stoi(argv[2]);
    // Check if user requested model generation
    bool produce_model = (argc >= 4 && string(argv[3]) == "--model");

    // Parse DIMACS file
    ifstream infile(filename);
    string line;
    int num_nodes = 0, num_edges = 0;
    vector<pair<int, int>> edges;

    while (getline(infile, line)) {
        if (line.empty() || line[0] == 'c') continue;
        if (line[0] == 'p') {
            string p, edge;
            stringstream ss(line);
            ss >> p >> edge >> num_nodes >> num_edges;
        } else if (line[0] == 'e') {
            char e;
            int u, v;
            stringstream ss(line);
            ss >> e >> u >> v;
            edges.push_back({u, v});
        }
    }

    // Initialize smt-switch cvc5 backend
    SmtSolver solver = Cvc5SolverFactory::create(false);
    // Enable model production inside cvc5 if flag is set
    if (produce_model) {
        solver->set_opt("produce-models", "true");
    }
    solver->set_logic("QF_LIA");
    Sort int_sort = solver->make_sort(INT);

    // Create variables for each node's color
    vector<Term> colors(num_nodes + 1);
    for (int i = 1; i <= num_nodes; i++) {
        colors[i] = solver->make_symbol("node_" + to_string(i), int_sort);
        
        // Constraint: 1 <= color <= K
        Term c_ge_1 = solver->make_term(Ge, colors[i], solver->make_term(1, int_sort));
        Term c_le_k = solver->make_term(Le, colors[i], solver->make_term(K, int_sort));
        solver->assert_formula(c_ge_1);
        solver->assert_formula(c_le_k);
    }

    // Constraint: Adjacent nodes have different colors
    for (auto edge : edges) {
        Term u_color = colors[edge.first];
        Term v_color = colors[edge.second];
        Term not_equal = solver->make_term(Not, solver->make_term(Equal, u_color, v_color));
        solver->assert_formula(not_equal);
    }

    // ---------------------------------------------------------
    // CLIQUE SYMMETRY BREAKING CONSTRAINTS
    // ---------------------------------------------------------
    if (num_nodes >= 1 && K >= 1) {
        // 1. Build an adjacency matrix for fast O(1) edge lookups
        vector<vector<bool>> adj(num_nodes + 1, vector<bool>(num_nodes + 1, false));
        for (auto edge : edges) {
            adj[edge.first][edge.second] = true;
            adj[edge.second][edge.first] = true;
        }

        // 2. Find a maximal clique using a greedy approach
        vector<int> clique;
        for (int i = 1; i <= num_nodes; i++) {
            bool connected_to_all = true;
            for (int v : clique) {
                if (!adj[i][v]) {
                    connected_to_all = false;
                    break;
                }
            }
            
            if (connected_to_all) {
                clique.push_back(i);
                // We only have K colors. If the clique size reaches K, we stop.
                // (If a clique is strictly larger than K, the graph is mathematically UNSAT).
                if (clique.size() == static_cast<size_t>(K)) {
                    break; 
                }
            }
        }

        // 3. Lock the colors of the clique nodes
        // Node 1 in clique -> Color 1
        // Node 2 in clique -> Color 2, etc.
        for (size_t i = 0; i < clique.size(); i++) {
            int node = clique[i];
            int assigned_color = i + 1;
            Term force_color = solver->make_term(Equal, colors[node], solver->make_term(assigned_color, int_sort));
            solver->assert_formula(force_color);
        }
    }
    // ---------------------------------------------------------

    // Check satisfiability
    Result res = solver->check_sat();
    if (res.is_sat()) {
        cout << "SAT" << endl;
         if (produce_model) {
            cout << "MODEL: ";
            for (int i = 1; i <= num_nodes; i++) {
                cout << solver->get_value(colors[i])->to_string() << " ";
            }
            cout << endl;
        }
    } else if (res.is_unsat()) {
        cout << "UNSAT" << endl;
    } else {
        cout << "UNKNOWN" << endl;
    }

    return 0;
}