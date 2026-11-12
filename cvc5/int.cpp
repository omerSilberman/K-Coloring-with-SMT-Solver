// Integer encodings: LIA, IDL, INT-MOD, INT-POW2
#include "colorer.h"
#include "registry.h"

namespace {

// ============================================================================
// LINEAR INTEGER ARITHMETIC (LIA)
// ============================================================================
class LiaColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { solver.setLogic("QF_LIA"); }
    void build_variables_and_bounds() override {
        if (strategies_given()) {
            for (int c = 1; c <= K; c++) colors.push_back(tm.mkInteger(c));
        }
        cvc5::Sort int_sort = tm.getIntegerSort();
        cvc5::Term one = tm.mkInteger(1);
        cvc5::Term k_term = tm.mkInteger(K);

        for (int i = 1; i <= num_nodes; ++i) {
            node_vars[i] = tm.mkConst(int_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GEQ, {node_vars[i], one}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {node_vars[i], k_term}));
        }
    }
};

// ============================================================================
// INTEGER DIFFERENCE LOGIC (IDL)
// ============================================================================
// Same idea as LIA, but every atom must have the form x - y <op> c.
// A plain bound like x >= 1 is not a difference, so it is written against
// an extra "zero" variable: x - zero >= 1 and x - zero <= K.
// IDL is shift-invariant, so the color of node i is node_i - zero.
class IdlColorer : public Cvc5Colorer {
private:
    cvc5::Term zero;
public:
    using Cvc5Colorer::Cvc5Colorer;
public:
    bool supports_colors() const override { return true; }
    // the colors are node - zero = 1..K
    void fix_color(int node, int color) override {
        cvc5::Term diff = tm.mkTerm(cvc5::Kind::SUB, {node_vars[node], zero});
        solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {diff, tm.mkInteger(color + 1)}));
    }
    string color_value(int color) override { return to_string(color + 1); }
protected:
    void configure_theory() override { solver.setLogic("QF_IDL"); }
    void build_variables_and_bounds() override {
        cvc5::Sort int_sort = tm.getIntegerSort();
        cvc5::Term one = tm.mkInteger(1);
        cvc5::Term k_term = tm.mkInteger(K);
        zero = tm.mkConst(int_sort, "zero");

        for (int i = 1; i <= num_nodes; ++i) {
            node_vars[i] = tm.mkConst(int_sort, "node_" + to_string(i));
            cvc5::Term diff = tm.mkTerm(cvc5::Kind::SUB, {node_vars[i], zero});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GEQ, {diff, one}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {diff, k_term}));
        }
    }
    void print_model() override {
        // Print the shifted values so the colors are in 1..K like the other theories
        cvc5::Term zero_val = solver.getValue(zero);
        for (int i = 1; i <= num_nodes; i++) {
            cvc5::Term color = tm.mkTerm(cvc5::Kind::SUB, {solver.getValue(node_vars[i]), zero_val});
            cout << "node_" << i << ": " << solver.simplify(color).toString() << " ";
        }
    }
};

// ============================================================================
// INTEGERS MODULO K (an infinite domain folded onto K colors)
// ============================================================================
// Each node is an unbounded integer x, and its color is x mod K. Edges compare
// the residues, so the solver has to see past the infinitely many values of x.
class IntModColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
public:
    bool supports_colors() const override { return true; }
    // the colors are the residues 0..K-1
    void fix_color(int node, int color) override {
        solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {residue(node_vars[node]), tm.mkInteger(color)}));
    }
    string color_value(int color) override { return to_string(color); }
protected:
    void configure_theory() override { solver.setLogic("QF_LIA"); }
    void build_variables_and_bounds() override {
        cvc5::Sort int_sort = tm.getIntegerSort();
        for (int i = 1; i <= num_nodes; ++i) {
            node_vars[i] = tm.mkConst(int_sort, "node_" + to_string(i));
        }
    }
    cvc5::Term residue(const cvc5::Term& x) {
        return tm.mkTerm(cvc5::Kind::INTS_MODULUS, {x, tm.mkInteger(K)});
    }
    cvc5::Term edge_constraint(const cvc5::Term& u, const cvc5::Term& v) override {
        return tm.mkTerm(cvc5::Kind::DISTINCT, {residue(u), residue(v)});
    }
    void print_model() override {
        // The color is the residue (the raw x values may all differ)
        for (int i = 1; i <= num_nodes; i++) {
            cout << "node_" << i << ": " << solver.getValue(residue(node_vars[i])).toString() << " ";
        }
    }
};

// ============================================================================
// INTEGER POWERS OF TWO (int.pow2)
// ============================================================================
// Each node is x = 2^e with 0 <= e <= K-1, so the colors are 1, 2, 4, ..., 2^(K-1):
// the integer counterpart of BV-ONEHOT. int.pow2 is a cvc5 extension.
class IntPow2Colorer : public Cvc5Colorer {
private:
    vector<cvc5::Term> exponents;
public:
    using Cvc5Colorer::Cvc5Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { solver.setLogic("ALL"); }
    void build_variables_and_bounds() override {
        if (strategies_given()) {
            for (int c = 0; c < K; c++) colors.push_back(tm.mkTerm(cvc5::Kind::POW2, {tm.mkInteger(c)}));
        }
        cvc5::Sort int_sort = tm.getIntegerSort();
        exponents.resize(num_nodes + 1);
        for (int i = 1; i <= num_nodes; ++i) {
            exponents[i] = tm.mkConst(int_sort, "e_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GEQ, {exponents[i], tm.mkInteger(0)}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {exponents[i], tm.mkInteger(K - 1)}));
            node_vars[i] = tm.mkTerm(cvc5::Kind::POW2, {exponents[i]});
        }
    }
};

}  // namespace

void register_int(Cvc5Registry& registry) {
    registry.add("LIA", make<LiaColorer>());
    registry.add("IDL", make<IdlColorer>());
    registry.add("INT-MOD", make<IntModColorer>());
    registry.add("INT-POW2", make<IntPow2Colorer>());
}
