// Propositional encodings: BOOL-DIRECT, BOOL-DIRECT-AMO
#include "colorer.h"
#include "registry.h"

namespace {

// ============================================================================
// PROPOSITIONAL LOGIC (The direct SAT encoding)
// ============================================================================
// K Booleans per node, c_i_j = "node i has color j", in logic QF_SAT (no theory):
//   at least one color:   c_i_1 or ... or c_i_K                  (one clause per node)
//   edges:                not c_u_j or not c_v_j                 (one clause per edge and color)
//   at most one (AMO):    not c_i_a or not c_i_b, for a < b      (only in BOOL-DIRECT-AMO)
// Without AMO a node may get several colors, but every one of them differs from all
// colors of its neighbours, so any one gives a valid coloring (the model takes the
// smallest). This is what BV-ONEHOT becomes after bit-blasting, minus the arithmetic.
class BoolDirectColorer : public Cvc5Colorer {
private:
    bool at_most_one;
    vector<vector<cvc5::Term>> has_color;  // has_color[i][j-1] = c_i_j
public:
    BoolDirectColorer(int k, bool model, bool print, bool at_most_one)
        : Cvc5Colorer(k, model, print), at_most_one(at_most_one) {}
public:
    bool supports_colors() const override { return true; }
    // color j is the Boolean c_node_j; the model prints colors as 1..K
    void fix_color(int node, int color) override { solver.assertFormula(has_color[node][color]); }
    string color_value(int color) override { return to_string(color + 1); }
protected:
    void configure_theory() override { solver.setLogic("QF_SAT"); }
    void build_variables_and_bounds() override {
        cvc5::Sort bool_sort = tm.getBooleanSort();
        has_color.resize(num_nodes + 1);
        for (int i = 1; i <= num_nodes; i++) {
            for (int j = 1; j <= K; j++) {
                has_color[i].push_back(tm.mkConst(bool_sort, "c_" + to_string(i) + "_" + to_string(j)));
            }
            solver.assertFormula(K == 1 ? has_color[i][0] : tm.mkTerm(cvc5::Kind::OR, has_color[i]));
            if (at_most_one) {
                for (int a = 0; a < K; a++) {
                    for (int b = a + 1; b < K; b++) {
                        solver.assertFormula(not_both(has_color[i][a], has_color[i][b]));
                    }
                }
            }
        }
    }
    cvc5::Term not_both(const cvc5::Term& x, const cvc5::Term& y) {
        return tm.mkTerm(cvc5::Kind::OR, {tm.mkTerm(cvc5::Kind::NOT, {x}), tm.mkTerm(cvc5::Kind::NOT, {y})});
    }
    cvc5::Term edge_constraint_between(int u, int v) override {
        vector<cvc5::Term> clauses;
        for (int j = 0; j < K; j++) clauses.push_back(not_both(has_color[u][j], has_color[v][j]));
        return K == 1 ? clauses[0] : tm.mkTerm(cvc5::Kind::AND, clauses);
    }
    void print_model() override {
        // A node's color is its smallest true c_i_j
        for (int i = 1; i <= num_nodes; i++) {
            int color = 0;
            for (int j = 0; j < K && color == 0; j++) {
                if (solver.getValue(has_color[i][j]).getBooleanValue()) color = j + 1;
            }
            cout << "node_" << i << ": " << color << " ";
        }
    }
};

}  // namespace

void register_bool(Cvc5Registry& registry) {
    registry.add("BOOL-DIRECT", make<BoolDirectColorer>(false));
    registry.add("BOOL-DIRECT-AMO", make<BoolDirectColorer>(true));
}
