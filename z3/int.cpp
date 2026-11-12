// Integer encodings: LIA, IDL, INT-MOD, INT-POW2 (see cvc5/int.cpp for the details)
#include "colorer.h"
#include "registry.h"

namespace {

// 1 <= x <= K
class LiaColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("QF_LIA"); }
    void build_variables_and_bounds() override {
        if (strategies_given()) {
            for (int c = 1; c <= K; c++) colors.push_back(ctx.int_val(c));
        }
        for (int i = 1; i <= num_nodes; ++i) {
            node_vars[i] = constant("node_" + to_string(i), ctx.int_sort());
            solver.add(node_vars[i] >= 1);
            solver.add(node_vars[i] <= K);
        }
    }
};

// Difference logic: 1 <= x - zero <= K; the color of node i is node_i - zero
class IdlColorer : public Z3Colorer {
private:
    optional<z3::expr> zero;
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
    // the colors are node - zero = 1..K
    void fix_color(int node, int color) override { solver.add(node_vars[node] - *zero == color + 1); }
    string color_value(int color) override { return to_string(color + 1); }
protected:
    void configure_theory() override { set_logic("QF_IDL"); }
    void build_variables_and_bounds() override {
        zero = constant("zero", ctx.int_sort());
        for (int i = 1; i <= num_nodes; ++i) {
            node_vars[i] = constant("node_" + to_string(i), ctx.int_sort());
            z3::expr diff = node_vars[i] - *zero;
            solver.add(diff >= 1);
            solver.add(diff <= K);
        }
    }
    void print_model() override {
        // The shifted values, so the colors are in 1..K like the other theories
        for (int i = 1; i <= num_nodes; i++) {
            cout << "node_" << i << ": " << value(node_vars[i] - *zero).to_string() << " ";
        }
    }
};

// Unbounded x, color x mod K
class IntModColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
    // the colors are the residues 0..K-1
    void fix_color(int node, int color) override { solver.add(residue(node_vars[node]) == color); }
    string color_value(int color) override { return to_string(color); }
protected:
    void configure_theory() override { set_logic("QF_LIA"); }
    void build_variables_and_bounds() override {
        for (int i = 1; i <= num_nodes; ++i) {
            node_vars[i] = constant("node_" + to_string(i), ctx.int_sort());
        }
    }
    z3::expr residue(const z3::expr& x) { return z3::mod(x, K); }
    z3::expr edge_constraint(const z3::expr& u, const z3::expr& v) override {
        return residue(u) != residue(v);
    }
    void print_model() override {
        // The color is the residue (the raw x values may all differ)
        for (int i = 1; i <= num_nodes; i++) {
            cout << "node_" << i << ": " << value(residue(node_vars[i])).to_string() << " ";
        }
    }
};

// x = 2^e with 0 <= e <= K-1. Z3 has no int.pow2; its general power operator ^ is
// the closest equivalent (nonlinear, handled by Z3's nonlinear arithmetic)
class IntPow2Colorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("ALL"); }
    void build_variables_and_bounds() override {
        if (strategies_given()) {
            for (int c = 0; c < K; c++) colors.push_back(z3::pw(ctx.int_val(2), ctx.int_val(c)));
        }
        for (int i = 1; i <= num_nodes; ++i) {
            z3::expr e = constant("e_" + to_string(i), ctx.int_sort());
            solver.add(e >= 0);
            solver.add(e <= K - 1);
            node_vars[i] = z3::pw(ctx.int_val(2), e);
        }
    }
};

}  // namespace

void register_int(Z3Registry& registry) {
    registry.add("LIA", make<LiaColorer>());
    registry.add("IDL", make<IdlColorer>());
    registry.add("INT-MOD", make<IntModColorer>());
    registry.add("INT-POW2", make<IntPow2Colorer>());
}
