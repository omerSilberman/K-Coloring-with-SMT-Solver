// Representatives encodings: REP, REP-BV (see the README, "REP")
#include <algorithm>

#include "colorer.h"
#include "registry.h"

namespace {

// ============================================================================
// REPRESENTATIVES (no color names, so no symmetric colorings)
// ============================================================================
// Each color class is named by its smallest node, its representative, instead of by one
// of K colors. A coloring has exactly one such description, where the color-numbering
// encodings have K! (one per renaming of the colors). Node u may represent v only if
// u < v and u, v are not adjacent (the asymmetric representatives formulation of
// Campêlo, Campos and Corrêa), and at most K nodes are representatives.
//
// The model numbers the classes 1, 2, ... in the order of their representatives.
// Strategies: fixing a clique's colors only breaks the symmetry between colors, which this
// formulation does not have, so fix_color asserts nothing; peel's repair uses 1..K.
class RepColorer : public Cvc5Colorer {
protected:
    vector<vector<bool>> adjacent;  // adjacent[u][v]

    RepColorer(int k, bool model, bool print) : Cvc5Colorer(k, model, print) {}

    void graph_loaded() override {
        Cvc5Colorer::graph_loaded();
        adjacent.assign(num_nodes + 1, vector<bool>(num_nodes + 1, false));
        for (const auto& [u, v] : edges) adjacent[u][v] = adjacent[v][u] = true;
    }
    // u can represent v
    bool may_represent(int u, int v) const { return u < v && !adjacent[u][v]; }

    // rep[v] = the representative of v (0 if none), printed as class numbers 1, 2, ...
    void print_classes(const vector<int>& rep) {
        vector<int> number(num_nodes + 1, 0);
        int classes = 0;
        for (int v = 1; v <= num_nodes; v++) {
            int r = rep[v];
            if (r >= 1 && r <= num_nodes && number[r] == 0) number[r] = ++classes;
            cout << "node_" << v << ": " << (r >= 1 && r <= num_nodes ? number[r] : 0) << " ";
        }
    }

public:
    bool supports_colors() const override { return true; }
    void fix_color(int, int) override {}
    string color_value(int color) override { return to_string(color + 1); }
};

// REP: Booleans r_u_v = "u represents v" (r_v_v = "v is a representative"), in QF_SAT:
//   v has a representative:   r_v_v ∨ r_u1_v ∨ ... (the u that may represent v)
//   only representatives:     r_u_v → r_u_u
//   edges:                    ¬r_u_v ∨ ¬r_u_w   for edge (v, w) and every u that may
//                             represent both
//   at most K representatives: a sequential counter over r_1_1 ... r_n_n (Sinz 2005),
//                             n·K auxiliary Booleans s_i_j = "at least j among the first i"
// Like BOOL-DIRECT, a node may get several representatives; any one of them is valid
// (the model takes the smallest).
class RepBoolColorer : public RepColorer {
private:
    vector<vector<cvc5::Term>> rep;  // rep[u][v] = r_u_v, null if u cannot represent v
public:
    RepBoolColorer(int k, bool model, bool print) : RepColorer(k, model, print) {}
protected:
    void configure_theory() override { solver.setLogic("QF_SAT"); }
    cvc5::Term lit(const cvc5::Term& x, bool positive) { return positive ? x : tm.mkTerm(cvc5::Kind::NOT, {x}); }
    cvc5::Term clause(const vector<cvc5::Term>& literals) {
        return literals.size() == 1 ? literals[0] : tm.mkTerm(cvc5::Kind::OR, literals);
    }
    void build_variables_and_bounds() override {
        cvc5::Sort bool_sort = tm.getBooleanSort();
        rep.assign(num_nodes + 1, vector<cvc5::Term>(num_nodes + 1));
        for (int v = 1; v <= num_nodes; v++) {
            rep[v][v] = tm.mkConst(bool_sort, "r_" + to_string(v) + "_" + to_string(v));
            for (int u = 1; u < v; u++) {
                if (may_represent(u, v)) {
                    rep[u][v] = tm.mkConst(bool_sort, "r_" + to_string(u) + "_" + to_string(v));
                }
            }
        }
        for (int v = 1; v <= num_nodes; v++) {
            vector<cvc5::Term> options = {rep[v][v]};
            for (int u = 1; u < v; u++) {
                if (!rep[u][v].isNull()) {
                    options.push_back(rep[u][v]);
                    solver.assertFormula(clause({lit(rep[u][v], false), rep[u][u]}));
                }
            }
            solver.assertFormula(clause(options));
        }
        at_most_k_representatives(bool_sort);
    }
    void at_most_k_representatives(const cvc5::Sort& bool_sort) {
        int n = num_nodes;
        if (K >= n) return;
        // s[i][j] (i = 1..n-1, j = 1..K): at least j representatives among nodes 1..i
        vector<vector<cvc5::Term>> s(n, vector<cvc5::Term>(K + 1));
        for (int i = 1; i < n; i++) {
            for (int j = 1; j <= K; j++) s[i][j] = tm.mkConst(bool_sort, "s_" + to_string(i) + "_" + to_string(j));
        }
        auto x = [&](int i) { return rep[i][i]; };
        solver.assertFormula(clause({lit(x(1), false), s[1][1]}));
        for (int j = 2; j <= K; j++) solver.assertFormula(lit(s[1][j], false));
        for (int i = 2; i < n; i++) {
            solver.assertFormula(clause({lit(x(i), false), s[i][1]}));
            solver.assertFormula(clause({lit(s[i - 1][1], false), s[i][1]}));
            for (int j = 2; j <= K; j++) {
                solver.assertFormula(clause({lit(x(i), false), lit(s[i - 1][j - 1], false), s[i][j]}));
                solver.assertFormula(clause({lit(s[i - 1][j], false), s[i][j]}));
            }
            solver.assertFormula(clause({lit(x(i), false), lit(s[i - 1][K], false)}));
        }
        solver.assertFormula(clause({lit(x(n), false), lit(s[n - 1][K], false)}));
    }
    cvc5::Term edge_constraint_between(int v, int w) override {
        vector<cvc5::Term> clauses;
        for (int u = 1; u < min(v, w); u++) {
            if (!rep[u][v].isNull() && !rep[u][w].isNull()) {
                clauses.push_back(clause({lit(rep[u][v], false), lit(rep[u][w], false)}));
            }
        }
        if (clauses.empty()) return cvc5::Term();
        return clauses.size() == 1 ? clauses[0] : tm.mkTerm(cvc5::Kind::AND, clauses);
    }
    void print_model() override {
        vector<int> chosen(num_nodes + 1, 0);
        for (int v = 1; v <= num_nodes; v++) {
            for (int u = 1; u <= v && chosen[v] == 0; u++) {
                if (!rep[u][v].isNull() && solver.getValue(rep[u][v]).getBooleanValue()) chosen[v] = u;
            }
        }
        print_classes(chosen);
    }
};

// REP-BV: one bit-vector per node, its representative's number, in QF_BV:
//   domain:     p_v = v ∨ p_v = u1 ∨ ...   (the u that may represent v)
//   closure:    p_v = u → p_u = u          (a representative represents itself)
//   edges:      p_v ≠ p_w                  (one per edge, like BV)
//   at most K:  ite(p_1 = 1, 1, 0) + ... + ite(p_n = n, 1, 0) ≤ K
// Smaller than REP: an edge is one disequality, not one clause per node that may represent
// both ends.
class RepBvColorer : public RepColorer {
public:
    RepBvColorer(int k, bool model, bool print) : RepColorer(k, model, print) {}
protected:
    void configure_theory() override {
        solver.setLogic("QF_BV");
        // cvc5's default (lazy) bit-blasting gets stuck on this formula: on myciel4, K = 4
        // it had not answered after 100 s; eager bit-blasting answers in 0.1 s
        solver.setOption("bitblast", "eager");
    }
    static uint32_t bits_for(int value) {
        uint32_t w = 1;
        while ((1LL << w) <= value) w++;
        return w;
    }
    void build_variables_and_bounds() override {
        uint32_t width = bits_for(num_nodes);
        cvc5::Sort sort = tm.mkBitVectorSort(width);
        auto node = [&](int v) { return tm.mkBitVector(width, v); };
        for (int v = 1; v <= num_nodes; v++) node_vars[v] = tm.mkConst(sort, "p_" + to_string(v));
        vector<cvc5::Term> is_representative;
        for (int v = 1; v <= num_nodes; v++) {
            cvc5::Term self = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[v], node(v)});
            vector<cvc5::Term> options = {self};
            for (int u = 1; u < v; u++) {
                if (!may_represent(u, v)) continue;
                cvc5::Term points = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[v], node(u)});
                options.push_back(points);
                solver.assertFormula(tm.mkTerm(cvc5::Kind::IMPLIES,
                                               {points, tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[u], node(u)})}));
            }
            solver.assertFormula(options.size() == 1 ? self : tm.mkTerm(cvc5::Kind::OR, options));
            is_representative.push_back(self);
        }
        if (K >= num_nodes) return;
        uint32_t count_width = bits_for(num_nodes);
        cvc5::Term one = tm.mkBitVector(count_width, 1), zero = tm.mkBitVector(count_width, 0);
        vector<cvc5::Term> counts;
        for (const auto& self : is_representative) counts.push_back(tm.mkTerm(cvc5::Kind::ITE, {self, one, zero}));
        cvc5::Term total = counts.size() == 1 ? counts[0] : tm.mkTerm(cvc5::Kind::BITVECTOR_ADD, counts);
        solver.assertFormula(tm.mkTerm(cvc5::Kind::BITVECTOR_ULE, {total, tm.mkBitVector(count_width, K)}));
    }
    void print_model() override {
        vector<int> chosen(num_nodes + 1, 0);
        for (int v = 1; v <= num_nodes; v++) {
            chosen[v] = (int)stoul(solver.getValue(node_vars[v]).getBitVectorValue(10));
        }
        print_classes(chosen);
    }
};

}  // namespace

void register_rep(Cvc5Registry& registry) {
    registry.add("REP", make<RepBoolColorer>());
    registry.add("REP-BV", make<RepBvColorer>());
}
