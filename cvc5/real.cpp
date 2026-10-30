// Real-arithmetic encodings: NLRA, NLRA-SQRT, NLRA-ROOTS and the trig roots NLRA-SIN, NLRA-COS, NLRA-SINCOS, NLRA-SINPI
#include "colorer.h"
#include "registry.h"

namespace {

// ============================================================================
// NON-LINEAR REAL ARITHMETIC (NLRA)
// ============================================================================
class NlraColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_NRA"); }
    void build_variables_and_bounds() override {
        cvc5::Sort real_sort = tm.getRealSort();
        cvc5::Term zero = tm.mkReal("0");
        
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(real_sort, "node_" + to_string(i));
            vector<cvc5::Term> roots;
            for (int c = 1; c <= K; c++) {
                cvc5::Term c_term = tm.mkReal(to_string(c));
                roots.push_back(tm.mkTerm(cvc5::Kind::SUB, {node_vars[i], c_term}));
            }
            cvc5::Term polynomial = tm.mkTerm(cvc5::Kind::MULT, roots);
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {polynomial, zero}));
        }
    }
};

// ============================================================================
// NON-LINEAR REAL ARITHMETIC (Irrational but algebraic colors: square roots)
// ============================================================================
// Each node is x > 0 with (x^2 - 1)(x^2 - 2)...(x^2 - K) = 0, so the colors are
// sqrt(1), ..., sqrt(K). Most are irrational like the trig roots, but algebraic,
// which cvc5's coverings solver represents exactly (unlike pi).
class NlraSqrtColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_NRA"); }
    void build_variables_and_bounds() override {
        cvc5::Sort real_sort = tm.getRealSort();
        cvc5::Term zero = tm.mkReal("0");

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(real_sort, "node_" + to_string(i));
            cvc5::Term square = tm.mkTerm(cvc5::Kind::MULT, {node_vars[i], node_vars[i]});
            vector<cvc5::Term> factors;
            for (int c = 1; c <= K; c++) {
                factors.push_back(tm.mkTerm(cvc5::Kind::SUB, {square, tm.mkReal(to_string(c))}));
            }
            cvc5::Term polynomial = (K == 1) ? factors[0] : tm.mkTerm(cvc5::Kind::MULT, factors);
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GT, {node_vars[i], zero}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {polynomial, zero}));
        }
    }
};

// ============================================================================
// NON-LINEAR REAL ARITHMETIC (Complex K-th roots of unity as points (a, b))
// ============================================================================
// Each node is a point (a, b) on the unit circle with (a + bi)^K = 1, i.e. a corner
// of the regular K-gon. (a + bi)^K is expanded into its real and imaginary parts,
// two real polynomials of degree K. The corners are cos(2 pi j/K) + i sin(2 pi j/K):
// the trig encoding again, but every coordinate is algebraic.
// Two nodes differ if a or b differs.
class NlraRootsColorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> a_vars, b_vars;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_NRA"); }
    void build_variables_and_bounds() override {
        cvc5::Sort real_sort = tm.getRealSort();
        cvc5::Term zero = tm.mkReal("0");
        cvc5::Term one = tm.mkReal("1");
        a_vars.resize(num_nodes + 1);
        b_vars.resize(num_nodes + 1);

        for (int i = 1; i <= num_nodes; i++) {
            cvc5::Term a = a_vars[i] = tm.mkConst(real_sort, "a_" + to_string(i));
            cvc5::Term b = b_vars[i] = tm.mkConst(real_sort, "b_" + to_string(i));
            // (re + im i)(a + b i) = (re a - im b) + (re b + im a) i, K - 1 times
            cvc5::Term re = a, im = b;
            for (int e = 2; e <= K; e++) {
                cvc5::Term next_re = tm.mkTerm(cvc5::Kind::SUB,
                    {tm.mkTerm(cvc5::Kind::MULT, {re, a}), tm.mkTerm(cvc5::Kind::MULT, {im, b})});
                cvc5::Term next_im = tm.mkTerm(cvc5::Kind::ADD,
                    {tm.mkTerm(cvc5::Kind::MULT, {re, b}), tm.mkTerm(cvc5::Kind::MULT, {im, a})});
                re = next_re;
                im = next_im;
            }
            // |z| = 1 follows from z^K = 1, but stating it helps the solver
            cvc5::Term norm = tm.mkTerm(cvc5::Kind::ADD,
                {tm.mkTerm(cvc5::Kind::MULT, {a, a}), tm.mkTerm(cvc5::Kind::MULT, {b, b})});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {norm, one}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {re, one}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {im, zero}));
        }
    }
    cvc5::Term edge_constraint_between(int u, int v) override {
        return tm.mkTerm(cvc5::Kind::OR,
            {tm.mkTerm(cvc5::Kind::DISTINCT, {a_vars[u], a_vars[v]}),
             tm.mkTerm(cvc5::Kind::DISTINCT, {b_vars[u], b_vars[v]})});
    }
    void print_model() override {
        for (int i = 1; i <= num_nodes; i++) {
            cout << "node_" << i << ": (" << solver.getValue(a_vars[i]).toString() << ", "
                 << solver.getValue(b_vars[i]).toString() << ") ";
        }
    }
};

// ============================================================================
// NON-LINEAR REAL ARITHMETIC + TRANSCENDENTALS (Roots of a trig function)
// ============================================================================
// Each node is a real x with f(x) = 0, boxed so the box holds exactly K roots.
// The roots of f are evenly spaced, `step` apart, starting at `offset`:
//   sin       roots at n*pi          (step pi,   offset 0)
//   cos       roots at pi/2 + n*pi   (step pi,   offset pi/2)
//   sin*cos   roots at n*pi/2        (step pi/2, offset 0)
// The box is offset + [-lo*step, hi*step] with lo + hi = K - 1,
// e.g. K = 7 with sin gives -3pi <= x <= 3pi.
class TrigColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    cvc5::Term pi;

    virtual cvc5::Term trig_function(const cvc5::Term& x) = 0;
    virtual cvc5::Term root_step() { return pi; }
    virtual cvc5::Term root_offset() { return tm.mkReal("0"); }

    void configure_theory() override { solver.setLogic("QF_NRAT"); }
    void build_variables_and_bounds() override {
        cvc5::Sort real_sort = tm.getRealSort();
        cvc5::Term zero = tm.mkReal("0");
        pi = tm.mkPi();

        int lo = (K - 1) / 2;
        int hi = (K - 1) - lo;
        cvc5::Term step = root_step();
        cvc5::Term offset = root_offset();
        cvc5::Term lower = tm.mkTerm(cvc5::Kind::SUB,
            {offset, tm.mkTerm(cvc5::Kind::MULT, {tm.mkReal(to_string(lo)), step})});
        cvc5::Term upper = tm.mkTerm(cvc5::Kind::ADD,
            {offset, tm.mkTerm(cvc5::Kind::MULT, {tm.mkReal(to_string(hi)), step})});

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(real_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GEQ, {node_vars[i], lower}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {node_vars[i], upper}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {trig_function(node_vars[i]), zero}));
        }
    }
};

class SinColorer : public TrigColorer {
public:
    using TrigColorer::TrigColorer;
protected:
    cvc5::Term trig_function(const cvc5::Term& x) override {
        return tm.mkTerm(cvc5::Kind::SINE, {x});
    }
};

class CosColorer : public TrigColorer {
public:
    using TrigColorer::TrigColorer;
protected:
    cvc5::Term trig_function(const cvc5::Term& x) override {
        return tm.mkTerm(cvc5::Kind::COSINE, {x});
    }
    cvc5::Term root_offset() override {
        return tm.mkTerm(cvc5::Kind::DIVISION, {pi, tm.mkReal("2")});
    }
};

class SinCosColorer : public TrigColorer {
public:
    using TrigColorer::TrigColorer;
protected:
    cvc5::Term trig_function(const cvc5::Term& x) override {
        return tm.mkTerm(cvc5::Kind::MULT,
            {tm.mkTerm(cvc5::Kind::SINE, {x}), tm.mkTerm(cvc5::Kind::COSINE, {x})});
    }
    cvc5::Term root_step() override {
        return tm.mkTerm(cvc5::Kind::DIVISION, {pi, tm.mkReal("2")});
    }
};

// ============================================================================
// NON-LINEAR REAL ARITHMETIC + TRANSCENDENTALS (Integer roots of sin(pi*x))
// ============================================================================
// sin(pi*x) = 0 exactly when x is an integer, so the colors are rational:
// x is boxed to [-lo, hi] with lo + hi = K - 1, e.g. K = 3 gives -1 <= x <= 1.
class SinPiColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_NRAT"); }
    void build_variables_and_bounds() override {
        cvc5::Sort real_sort = tm.getRealSort();
        cvc5::Term zero = tm.mkReal("0");
        cvc5::Term pi = tm.mkPi();

        int lo = (K - 1) / 2;
        int hi = (K - 1) - lo;
        cvc5::Term lower = tm.mkReal(to_string(-lo));
        cvc5::Term upper = tm.mkReal(to_string(hi));

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(real_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GEQ, {node_vars[i], lower}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {node_vars[i], upper}));
            cvc5::Term arg = tm.mkTerm(cvc5::Kind::MULT, {pi, node_vars[i]});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {tm.mkTerm(cvc5::Kind::SINE, {arg}), zero}));
        }
    }
};

}  // namespace

void register_real(Registry& registry) {
    registry.add("NLRA", make<NlraColorer>());
    registry.add("NLRA-SQRT", make<NlraSqrtColorer>());
    registry.add("NLRA-ROOTS", make<NlraRootsColorer>());
    registry.add("NLRA-SIN", make<SinColorer>());
    registry.add("NLRA-COS", make<CosColorer>());
    registry.add("NLRA-SINCOS", make<SinCosColorer>());
    registry.add("NLRA-SINPI", make<SinPiColorer>());
}
