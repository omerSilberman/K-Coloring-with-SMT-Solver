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
        cerr << "Usage: ./smt_solver_bv <dimacs_file> <K> [--model]" << endl;
        return 1;
    }

    string filename = argv[1];
    int K = stoi(argv[2]);
    bool produce_model = (argc >= 4 && string(argv[3]) == "--model");

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

    SmtSolver solver = Cvc5SolverFactory::create(false);
    if (produce_model) {
        solver->set_opt("produce-models", "true");
    }
    
    // ---------------------------------------------------------
    // BIT-VECTOR LOGIC
    // ---------------------------------------------------------
    solver->set_logic("QF_BV");
    
    // Calculate the absolute minimum number of bits needed to hold K
    // For K=6, width becomes 3 because (2^3)-1 = 7, which can hold 6.
    int width = 1;
    while ((1 << width) - 1 < K) {
        width++;
    }
    
    Sort bv_sort = solver->make_sort(BV, width);

    vector<Term> colors(num_nodes + 1);
    for (int i = 1; i <= num_nodes; i++) {
        colors[i] = solver->make_symbol("node_" + to_string(i), bv_sort);
        
        // In smt-switch, we initialize BV constants via strings in base 10
        Term one = solver->make_term(to_string(1), bv_sort, 10);
        Term k_term = solver->make_term(to_string(K), bv_sort, 10);
        
        // BVUge = Bit-Vector Unsigned Greater or Equal
        // BVUle = Bit-Vector Unsigned Less or Equal
        Term c_ge_1 = solver->make_term(BVUge, colors[i], one);
        Term c_le_k = solver->make_term(BVUle, colors[i], k_term);
        
        solver->assert_formula(c_ge_1);
        solver->assert_formula(c_le_k);
    }

    for (auto edge : edges) {
        Term not_equal = solver->make_term(Not, solver->make_term(Equal, colors[edge.first], colors[edge.second]));
        solver->assert_formula(not_equal);
    }
    // ---------------------------------------------------------

    Result res = solver->check_sat();
    if (res.is_sat()) {
        cout << "SAT" << endl;
        if (produce_model) {
            cout << "MODEL: ";
            for (int i = 1; i <= num_nodes; i++) {
                // Note: BV models usually output as binary strings (e.g., #b010)
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