// Real-arithmetic encodings: NLRA, NLRA-SQRT, NLRA-ROOTS (see cvc5/real.cpp and the README).
// The trig encodings (NLRA-SIN, -COS, -SINCOS, -SINPI) are not here: Z3's C++ API has no
// sine, and its solver answers unknown even with a root pinned to a small interval.
#include "colorer.h"
#include "registry.h"

namespace {

// (x - 1)(x - 2)...(x - K) = 0
class NlraColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_NRA"); }
    void build_variables_and_bounds() override {
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.real_sort());
            z3::expr polynomial = node_vars[i] - ctx.real_val(1);
            for (int c = 2; c <= K; c++) polynomial = polynomial * (node_vars[i] - ctx.real_val(c));
            solver.add(polynomial == ctx.real_val(0));
        }
    }
};

// x > 0 and (x^2 - 1)(x^2 - 2)...(x^2 - K) = 0: the colors are sqrt(1), ..., sqrt(K)
class NlraSqrtColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_NRA"); }
    void build_variables_and_bounds() override {
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.real_sort());
            z3::expr square = node_vars[i] * node_vars[i];
            z3::expr polynomial = square - ctx.real_val(1);
            for (int c = 2; c <= K; c++) polynomial = polynomial * (square - ctx.real_val(c));
            solver.add(node_vars[i] > ctx.real_val(0));
            solver.add(polynomial == ctx.real_val(0));
        }
    }
};

// A point (a, b) with (a + bi)^K = 1 and a^2 + b^2 = 1: a corner of the regular K-gon
class NlraRootsColorer : public Z3Colorer {
private:
    vector<z3::expr> a_vars, b_vars;
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_NRA"); }
    void build_variables_and_bounds() override {
        a_vars.assign(num_nodes + 1, ctx.real_val(0));
        b_vars.assign(num_nodes + 1, ctx.real_val(0));
        for (int i = 1; i <= num_nodes; i++) {
            z3::expr a = a_vars[i] = constant("a_" + to_string(i), ctx.real_sort());
            z3::expr b = b_vars[i] = constant("b_" + to_string(i), ctx.real_sort());
            // (re + im i)(a + b i) = (re a - im b) + (re b + im a) i, K - 1 times
            z3::expr re = a, im = b;
            for (int e = 2; e <= K; e++) {
                z3::expr next_re = re * a - im * b;
                z3::expr next_im = re * b + im * a;
                re = next_re;
                im = next_im;
            }
            // |z| = 1 follows from z^K = 1, but stating it helps the solver
            solver.add(a * a + b * b == ctx.real_val(1));
            solver.add(re == ctx.real_val(1));
            solver.add(im == ctx.real_val(0));
        }
    }
    optional<z3::expr> edge_constraint_between(int u, int v) override {
        return a_vars[u] != a_vars[v] || b_vars[u] != b_vars[v];
    }
    void print_model() override {
        for (int i = 1; i <= num_nodes; i++) {
            cout << "node_" << i << ": (" << value(a_vars[i]).to_string() << ", "
                 << value(b_vars[i]).to_string() << ") ";
        }
    }
};

}  // namespace

void register_real(Z3Registry& registry) {
    registry.add("NLRA", make<NlraColorer>());
    registry.add("NLRA-SQRT", make<NlraSqrtColorer>());
    registry.add("NLRA-ROOTS", make<NlraRootsColorer>());
}
