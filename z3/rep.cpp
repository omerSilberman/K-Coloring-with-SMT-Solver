// Representatives encodings: REP, REP-PB, REP-BV (see cvc5/rep.cpp and the README, "REP")
#include <algorithm>

#include "colorer.h"
#include "registry.h"

namespace {

// Each color class is named by its smallest node, its representative: u may represent v
// only if u < v and u, v are not adjacent, and at most K nodes are representatives. A
// coloring has exactly one such description, so there are no renamings of the colors to
// search through. The model numbers the classes 1, 2, ... in the order of their
// representatives; fix_color asserts nothing (no color symmetry to break).
class RepColorer : public Z3Colorer {
protected:
    vector<vector<bool>> adjacent;

    RepColorer(int k, bool model, bool print) : Z3Colorer(k, model, print) {}

    void graph_loaded() override {
        Z3Colorer::graph_loaded();
        adjacent.assign(num_nodes + 1, vector<bool>(num_nodes + 1, false));
        for (const auto& [u, v] : edges) adjacent[u][v] = adjacent[v][u] = true;
    }
    bool may_represent(int u, int v) const { return u < v && !adjacent[u][v]; }

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

// REP and REP-PB: Booleans r_u_v = "u represents v", in QF_FD:
//   r_v_v ∨ r_u1_v ∨ ...,   r_u_v → r_u_u,   ¬r_u_v ∨ ¬r_u_w per edge (v, w) and common u
//   at most K of r_1_1 ... r_n_n: a sequential counter in clauses (REP, as in cvc5) or
//   Z3's native pseudo-Boolean atmost (REP-PB)
class RepBoolColorer : public RepColorer {
private:
    bool native_count;
    vector<vector<optional<z3::expr>>> rep;
public:
    RepBoolColorer(int k, bool model, bool print, bool native_count)
        : RepColorer(k, model, print), native_count(native_count) {}
protected:
    void configure_theory() override { set_logic("QF_FD"); }
    void build_variables_and_bounds() override {
        rep.assign(num_nodes + 1, vector<optional<z3::expr>>(num_nodes + 1));
        for (int v = 1; v <= num_nodes; v++) {
            for (int u = 1; u <= v; u++) {
                if (u == v || may_represent(u, v)) {
                    rep[u][v] = constant("r_" + to_string(u) + "_" + to_string(v), ctx.bool_sort());
                }
            }
        }
        for (int v = 1; v <= num_nodes; v++) {
            vector<z3::expr> options = {*rep[v][v]};
            for (int u = 1; u < v; u++) {
                if (!rep[u][v]) continue;
                options.push_back(*rep[u][v]);
                solver.add(!*rep[u][v] || *rep[u][u]);
            }
            solver.add(any_of(options));
        }
        if (K >= num_nodes) return;
        vector<z3::expr> x;
        for (int v = 1; v <= num_nodes; v++) x.push_back(*rep[v][v]);
        if (native_count) {
            solver.add(z3::atmost(vec(x), K));
        } else {
            sequential_counter(x);
        }
    }
    // at most K of x (Sinz 2005): s[i][j] = "at least j among x_1..x_i"
    void sequential_counter(const vector<z3::expr>& x) {
        int n = x.size();
        vector<vector<z3::expr>> s(n, vector<z3::expr>(K + 1, ctx.bool_val(false)));
        for (int i = 1; i < n; i++) {
            for (int j = 1; j <= K; j++) s[i][j] = constant("s_" + to_string(i) + "_" + to_string(j), ctx.bool_sort());
        }
        auto X = [&](int i) { return x[i - 1]; };
        solver.add(!X(1) || s[1][1]);
        for (int j = 2; j <= K; j++) solver.add(!s[1][j]);
        for (int i = 2; i < n; i++) {
            solver.add(!X(i) || s[i][1]);
            solver.add(!s[i - 1][1] || s[i][1]);
            for (int j = 2; j <= K; j++) {
                solver.add(!X(i) || !s[i - 1][j - 1] || s[i][j]);
                solver.add(!s[i - 1][j] || s[i][j]);
            }
            solver.add(!X(i) || !s[i - 1][K]);
        }
        solver.add(!X(n) || !s[n - 1][K]);
    }
    optional<z3::expr> edge_constraint_between(int v, int w) override {
        vector<z3::expr> clauses;
        for (int u = 1; u < min(v, w); u++) {
            if (rep[u][v] && rep[u][w]) clauses.push_back(!*rep[u][v] || !*rep[u][w]);
        }
        if (clauses.empty()) return nullopt;
        return all_of(clauses);
    }
    void print_model() override {
        vector<int> chosen(num_nodes + 1, 0);
        for (int v = 1; v <= num_nodes; v++) {
            for (int u = 1; u <= v && chosen[v] == 0; u++) {
                if (rep[u][v] && value(*rep[u][v]).is_true()) chosen[v] = u;
            }
        }
        print_classes(chosen);
    }
};

// REP-BV: p_v = the representative's number, as a bit-vector, in QF_BV:
//   p_v = v ∨ p_v = u1 ∨ ...,   p_v = u → p_u = u,   p_v ≠ p_w per edge,
//   Σ ite(p_v = v, 1, 0) ≤ K
class RepBvColorer : public RepColorer {
public:
    RepBvColorer(int k, bool model, bool print) : RepColorer(k, model, print) {}
protected:
    void configure_theory() override { set_logic("QF_BV"); }
    static unsigned bits_for(int value) {
        unsigned w = 1;
        while ((1LL << w) <= value) w++;
        return w;
    }
    void build_variables_and_bounds() override {
        unsigned width = bits_for(num_nodes);
        auto node = [&](int v) { return ctx.bv_val(v, width); };
        for (int v = 1; v <= num_nodes; v++) node_vars[v] = constant("p_" + to_string(v), ctx.bv_sort(width));
        vector<z3::expr> counts;
        z3::expr one = ctx.bv_val(1, width), zero = ctx.bv_val(0, width);
        for (int v = 1; v <= num_nodes; v++) {
            z3::expr self = node_vars[v] == node(v);
            vector<z3::expr> options = {self};
            for (int u = 1; u < v; u++) {
                if (!may_represent(u, v)) continue;
                z3::expr points = node_vars[v] == node(u);
                options.push_back(points);
                solver.add(z3::implies(points, node_vars[u] == node(u)));
            }
            solver.add(any_of(options));
            counts.push_back(z3::ite(self, one, zero));
        }
        if (K >= num_nodes) return;
        z3::expr total = counts[0];
        for (size_t i = 1; i < counts.size(); i++) total = total + counts[i];
        solver.add(z3::ule(total, ctx.bv_val(K, width)));
    }
    void print_model() override {
        vector<int> chosen(num_nodes + 1, 0);
        for (int v = 1; v <= num_nodes; v++) chosen[v] = value(node_vars[v]).get_numeral_int();
        print_classes(chosen);
    }
};

}  // namespace

void register_rep(Z3Registry& registry) {
    registry.add("REP", make<RepBoolColorer>(false));
    registry.add("REP-PB", make<RepBoolColorer>(true));
    registry.add("REP-BV", make<RepBvColorer>());
}
