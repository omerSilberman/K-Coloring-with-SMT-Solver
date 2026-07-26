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
    solver->set_opt("produce-models", "true");
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
    // SYMMETRY BREAKING CONSTRAINTS
    // ---------------------------------------------------------
    if (num_nodes >= 1 && K >= 1) {
        // 1. Force Node 1 to always be Color 1
        Term force_c1 = solver->make_term(Equal, colors[1], solver->make_term(1, int_sort));
        solver->assert_formula(force_c1);

        // 2. Find the first neighbor of Node 1 and force it to be Color 2
        if (K >= 2) {
            for (auto edge : edges) {
                if (edge.first == 1 || edge.second == 1) {
                    int neighbor = (edge.first == 1) ? edge.second : edge.first;
                    Term force_c2 = solver->make_term(Equal, colors[neighbor], solver->make_term(2, int_sort));
                    solver->assert_formula(force_c2);
                    break; // Only break symmetry for the first neighbor found
                }
            }
        }
    }
    // ---------------------------------------------------------

    // Check satisfiability
    Result res = solver->check_sat();
    if (res.is_sat()) {
        cout << "SAT" << endl;
    } else if (res.is_unsat()) {
        cout << "UNSAT" << endl;
    } else {
        cout << "UNKNOWN" << endl;
    }

    return 0;
}