// Propositional encodings: BOOL-DIRECT, BOOL-DIRECT-AMO (see cvc5/bool.cpp and the README)
#include "colorer.h"
#include "registry.h"

namespace {

// K Booleans per node, c_i_j = "node i has color j":
//   at least one color:  c_i_1 or ... or c_i_K
//   edges:               not c_u_j or not c_v_j, per color
//   at most one (AMO):   not c_i_a or not c_i_b, a < b   (BOOL-DIRECT-AMO only)
// Z3 has no QF_SAT logic; QF_FD (finite domains) is its propositional/SAT-based logic.
class BoolDirectColorer : public Z3Colorer {
private:
    bool at_most_one;
    vector<vector<z3::expr>> has_color;  // has_color[i][j-1] = c_i_j
public:
    BoolDirectColorer(int k, bool model, bool print, bool at_most_one)
        : Z3Colorer(k, model, print), at_most_one(at_most_one) {}
protected:
    void configure_theory() override { set_logic("QF_FD"); }
    void build_variables_and_bounds() override {
        has_color.resize(num_nodes + 1);
        for (int i = 1; i <= num_nodes; i++) {
            for (int j = 1; j <= K; j++) {
                has_color[i].push_back(constant("c_" + to_string(i) + "_" + to_string(j), ctx.bool_sort()));
            }
            solver.add(any_of(has_color[i]));
            if (at_most_one) {
                for (int a = 0; a < K; a++) {
                    for (int b = a + 1; b < K; b++) solver.add(not_both(has_color[i][a], has_color[i][b]));
                }
            }
        }
    }
    z3::expr not_both(const z3::expr& x, const z3::expr& y) { return !x || !y; }
    optional<z3::expr> edge_constraint_between(int u, int v) override {
        vector<z3::expr> clauses;
        for (int j = 0; j < K; j++) clauses.push_back(not_both(has_color[u][j], has_color[v][j]));
        return all_of(clauses);
    }
    void print_model() override {
        // A node's color is its smallest true c_i_j
        for (int i = 1; i <= num_nodes; i++) {
            int color = 0;
            for (int j = 0; j < K && color == 0; j++) {
                if (value(has_color[i][j]).is_true()) color = j + 1;
            }
            cout << "node_" << i << ": " << color << " ";
        }
    }
};

}  // namespace

void register_bool(Z3Registry& registry) {
    registry.add("BOOL-DIRECT", make<BoolDirectColorer>(false));
    registry.add("BOOL-DIRECT-AMO", make<BoolDirectColorer>(true));
}
