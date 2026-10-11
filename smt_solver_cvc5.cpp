#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <stdexcept>
#include <cvc5/cvc5.h> // Native CVC5 API

using namespace std;

// ============================================================================
// 1. ABSTRACT BASE CLASS (Native CVC5)
// ============================================================================
class AbstractGraphColorer {
protected:
    int num_nodes = 0;
    int num_edges = 0;
    int K;
    bool produce_model;
    bool print_asserts;
    
    vector<pair<int, int>> edges;
    cvc5::TermManager tm; // CVC5 requires a TermManager
    cvc5::Solver solver;  // Native CVC5 Solver
    vector<cvc5::Term> node_vars;

public:
    AbstractGraphColorer(int k, bool model, bool print) 
        : K(k), produce_model(model), print_asserts(print), solver(tm) {
        if (produce_model) {
            solver.setOption("produce-models", "true");
        }
    }

    virtual ~AbstractGraphColorer() = default;

    void load_dimacs(const string& filename) {
        ifstream infile(filename);
        if (!infile.is_open()) {
            throw runtime_error("Could not open file: " + filename);
        }

        string line;
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
        node_vars.resize(num_nodes + 1);
    }

    void solve() {
        configure_theory();              
        build_variables_and_bounds();    
        build_universal_edge_constraints(); 

        if (print_asserts) {
            cout << "; --- ASSERTED FORMULAS ---" << endl;
            for (const auto& formula : solver.getAssertions()) {
                cout << "(assert " << formula.toString() << ")" << endl;
            }
            cout << "; -------------------------" << endl;
        }

        cvc5::Result res = solver.checkSat();

        if (res.isSat()) {
            cout << "SAT" << endl;
            if (produce_model) {
                cout << "MODEL: ";
                print_model();
                cout << endl;
            }
        } else if (res.isUnsat()) {
            cout << "UNSAT" << endl;
        } else {
            cout << "UNKNOWN" << endl;
        }
    }

protected:
    virtual void configure_theory() = 0;
    virtual void build_variables_and_bounds() = 0;
    virtual void print_model() {
        for (int i = 1; i <= num_nodes; i++) {
            cout << "node_" << i << ": " << solver.getValue(node_vars[i]).toString() << " ";
        }
}
    // The two endpoints of an edge get different colors (u != v unless overridden)
    virtual cvc5::Term edge_constraint(const cvc5::Term& u, const cvc5::Term& v) {
        return tm.mkTerm(cvc5::Kind::NOT, {tm.mkTerm(cvc5::Kind::EQUAL, {u, v})});
    }

private:
    void build_universal_edge_constraints() {
        for (const auto& edge : edges) {
            solver.assertFormula(edge_constraint(node_vars[edge.first], node_vars[edge.second]));
        }
    }
};

// ============================================================================
// 2. LINEAR INTEGER ARITHMETIC (LIA)
// ============================================================================
class LiaColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_LIA"); }
    void build_variables_and_bounds() override {
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
class IdlColorer : public AbstractGraphColorer {
private:
    cvc5::Term zero;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
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
// 3. BIT-VECTOR (BV)
// ============================================================================
// Colors 1..K: 1 <=u x <=u K, at the smallest width that holds K.
// When K = 2^w (K >= 2) the sort has exactly K values, so width w and no bounds.
class BvColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_BV"); }
    void build_variables_and_bounds() override {
        if (K >= 2 && (K & (K - 1)) == 0) {
            int width = 0;
            while ((1 << width) < K) { width++; }
            cvc5::Sort bv_sort = tm.mkBitVectorSort(width);
            for (int i = 1; i <= num_nodes; i++) {
                node_vars[i] = tm.mkConst(bv_sort, "node_" + to_string(i));
            }
            return;
        }

        int width = 1;
        while ((1 << width) - 1 < K) { width++; }
        cvc5::Sort bv_sort = tm.mkBitVectorSort(width);
        cvc5::Term one = tm.mkBitVector(width, 1);
        cvc5::Term k_term = tm.mkBitVector(width, K);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(bv_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::BITVECTOR_UGE, {node_vars[i], one}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::BITVECTOR_ULE, {node_vars[i], k_term}));
        }
    }
};

// Colors 0..K-1: only the upper bound x <=u K-1 (the lower bound 0 is free),
// at the smallest width w with 2^w >= K. When K = 2^w (K >= 2), no bound at all.
class BvZeroColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_BV"); }
    void build_variables_and_bounds() override {
        int width = 1;
        while ((1 << width) < K) { width++; }
        cvc5::Sort bv_sort = tm.mkBitVectorSort(width);
        bool needs_bound = (1 << width) != K;
        cvc5::Term max_term = tm.mkBitVector(width, K - 1);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(bv_sort, "node_" + to_string(i));
            if (needs_bound) {
                solver.assertFormula(tm.mkTerm(cvc5::Kind::BITVECTOR_ULE, {node_vars[i], max_term}));
            }
        }
    }
};

// ============================================================================
// BIT-VECTOR (Bitwise AND masks)
// ============================================================================
// Width w is the smallest with 2^w >= K, and E = 2^w - K values must be excluded.
// A literal (x & M) != 0 excludes exactly the values with 0 in every bit of M,
// i.e. the submasks of ~M. We exclude {0, ..., E-1}: a submask of n is <= n, so
// this set is closed under submasks and is the union of the submasks of its
// maximal elements. Each 1-bit b of E gives one maximal element
//   a_b = (E with bits b..0 cleared) | (2^b - 1)
// and one literal (x & ~a_b) != 0. The colors left are E, ..., 2^w - 1.
// K = 2^w needs no literal; K = 2^w - 2^j needs one; never more than w - 1.
class BvAndColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_BV"); }
    void build_variables_and_bounds() override {
        int width = 1;
        while ((1 << width) < K) { width++; }
        int full = (1 << width) - 1;
        int excluded = (1 << width) - K;

        cvc5::Sort bv_sort = tm.mkBitVectorSort(width);
        cvc5::Term zero = tm.mkBitVector(width, 0);
        vector<cvc5::Term> masks;
        for (int b = 0; b < width; b++) {
            if (excluded >> b & 1) {
                int maximal = ((excluded >> (b + 1)) << (b + 1)) | ((1 << b) - 1);
                masks.push_back(tm.mkBitVector(width, full & ~maximal));
            }
        }

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(bv_sort, "node_" + to_string(i));
            for (const auto& mask : masks) {
                cvc5::Term masked = tm.mkTerm(cvc5::Kind::BITVECTOR_AND, {node_vars[i], mask});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::DISTINCT, {masked, zero}));
            }
        }
    }
};

// ============================================================================
// BIT-VECTOR (One-hot colors)
// ============================================================================
// Width K, and color c is the vector with only bit c set:
//   x != 0 and (x & (x - 1)) = 0   (x - 1 clears the lowest set bit, so the AND
//                                    is 0 iff x had at most one set bit)
// Two one-hot vectors differ iff they share no bit, so edges are (u & v) = 0.
class BvOneHotColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_BV"); }
    void build_variables_and_bounds() override {
        cvc5::Sort bv_sort = tm.mkBitVectorSort(K);
        cvc5::Term zero = tm.mkBitVector(K, 0);
        cvc5::Term one = tm.mkBitVector(K, 1);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(bv_sort, "node_" + to_string(i));
            cvc5::Term x = node_vars[i];
            solver.assertFormula(tm.mkTerm(cvc5::Kind::DISTINCT, {x, zero}));
            cvc5::Term x_minus_1 = tm.mkTerm(cvc5::Kind::BITVECTOR_SUB, {x, one});
            cvc5::Term lowest_cleared = tm.mkTerm(cvc5::Kind::BITVECTOR_AND, {x, x_minus_1});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {lowest_cleared, zero}));
        }
    }
    cvc5::Term edge_constraint(const cvc5::Term& u, const cvc5::Term& v) override {
        cvc5::Term shared = tm.mkTerm(cvc5::Kind::BITVECTOR_AND, {u, v});
        return tm.mkTerm(cvc5::Kind::EQUAL, {shared, tm.mkBitVector(K, 0)});
    }
};

// ============================================================================
// 4. NON-LINEAR REAL ARITHMETIC (NLRA)
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

// ============================================================================
// FINITE FIELDS (GF(p), p prime - cvc5 needs to be built with --cocoa)
// ============================================================================
static bool is_prime(int n) {
    if (n < 2) return false;
    for (int d = 2; d * d <= n; d++) {
        if (n % d == 0) return false;
    }
    return true;
}

class FiniteFieldColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    int p = 0;
    cvc5::Sort ff_sort;

    // The field size to use for this K
    virtual int choose_modulus() = 0;
    // Constraint restricting x to K of the p field elements (null term = no constraint)
    virtual cvc5::Term domain_constraint(const cvc5::Term& x) = 0;

    cvc5::Term ff_const(int value) {
        return tm.mkFiniteFieldElem(to_string(((value % p) + p) % p), ff_sort);
    }

    void configure_theory() override { solver.setLogic("QF_FF"); }
    void build_variables_and_bounds() override {
        p = choose_modulus();
        ff_sort = tm.mkFiniteFieldSort(to_string(p));

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(ff_sort, "node_" + to_string(i));
            cvc5::Term constraint = domain_constraint(node_vars[i]);
            if (!constraint.isNull()) {
                solver.assertFormula(constraint);
            }
        }
    }
};

// GF(K) itself: the sort has exactly K elements, so no domain constraint at all
// (the paper's "finite domain of fixed size" colorer). Only works for prime K.
class FfPrimeColorer : public FiniteFieldColorer {
public:
    using FiniteFieldColorer::FiniteFieldColorer;
protected:
    int choose_modulus() override {
        if (!is_prime(K)) {
            throw runtime_error("FF-PRIME needs a prime K (got " + to_string(K) + ")");
        }
        return K;
    }
    cvc5::Term domain_constraint(const cvc5::Term&) override { return cvc5::Term(); }
};

// GF(p) with p the smallest prime >= K, and (x - 0)(x - 1)...(x - (K-1)) = 0.
// A field has no zero divisors, so the product is 0 iff x is one of 0..K-1.
// When p == K this is x^p - x, which holds for every x (Fermat).
class FfPolyColorer : public FiniteFieldColorer {
public:
    using FiniteFieldColorer::FiniteFieldColorer;
protected:
    int choose_modulus() override {
        int q = max(K, 2);
        while (!is_prime(q)) q++;
        return q;
    }
    cvc5::Term domain_constraint(const cvc5::Term& x) override {
        vector<cvc5::Term> factors;
        for (int j = 0; j < K; j++) {
            factors.push_back(j == 0 ? x : tm.mkTerm(cvc5::Kind::FINITE_FIELD_ADD, {x, ff_const(-j)}));
        }
        cvc5::Term product = (K == 1) ? factors[0] : tm.mkTerm(cvc5::Kind::FINITE_FIELD_MULT, factors);
        return tm.mkTerm(cvc5::Kind::EQUAL, {product, ff_const(0)});
    }
};

// GF(p) with p the smallest prime s.t. K divides p - 1, and x^K = 1.
// The nonzero elements form a cyclic group of order p - 1, so x^K = 1 has
// exactly K solutions: the K-th roots of unity (e.g. K = 3, p = 7 gives {1, 2, 4}).
class FfRootsColorer : public FiniteFieldColorer {
public:
    using FiniteFieldColorer::FiniteFieldColorer;
protected:
    int choose_modulus() override {
        int q = K + 1;
        while (!is_prime(q)) q += K;
        return q;
    }
    cvc5::Term domain_constraint(const cvc5::Term& x) override {
        // x^K by repeated squaring
        cvc5::Term result, square = x;
        for (int e = K; e > 0; e >>= 1) {
            if (e & 1) {
                result = result.isNull() ? square : tm.mkTerm(cvc5::Kind::FINITE_FIELD_MULT, {result, square});
            }
            if (e > 1) square = tm.mkTerm(cvc5::Kind::FINITE_FIELD_MULT, {square, square});
        }
        return tm.mkTerm(cvc5::Kind::EQUAL, {result, ff_const(1)});
    }
};

// ============================================================================
// 5. THEORY OF LISTS (Uninterpreted Functions)
// ============================================================================
class ListUfColorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> color_constants;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_UF"); }
    void build_variables_and_bounds() override {
        cvc5::Sort list_sort = tm.mkUninterpretedSort("List");
        cvc5::Term nil_val = tm.mkConst(list_sort, "nil");
        cvc5::Sort cons_sig = tm.mkFunctionSort({list_sort, list_sort}, list_sort);
        cvc5::Term cons_func = tm.mkConst(cons_sig, "cons");
        
        cvc5::Term current_color = tm.mkTerm(cvc5::Kind::APPLY_UF, {cons_func, nil_val, nil_val});
        color_constants.push_back(current_color);
        for (int i = 1; i < K; i++) {
            current_color = tm.mkTerm(cvc5::Kind::APPLY_UF, {cons_func, current_color, nil_val});
            color_constants.push_back(current_color);
        }
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) {
                cvc5::Term eq = tm.mkTerm(cvc5::Kind::EQUAL, {color_constants[i], color_constants[j]});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT, {eq}));
            }
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(list_sort, "node_" + to_string(i));
            cvc5::Term domain_constraint = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[0]});
            for (int c = 1; c < K; c++) {
                cvc5::Term is_color_c = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[c]});
                domain_constraint = tm.mkTerm(cvc5::Kind::OR, {domain_constraint, is_color_c});
            }
            solver.assertFormula(domain_constraint);
        }
    }
};

// ============================================================================
// 6. TRUE THEORY OF DATATYPES
// ============================================================================
class ListDtColorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> color_constants;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_DT"); }
    void build_variables_and_bounds() override {
        cvc5::DatatypeDecl color_decl = tm.mkDatatypeDecl("Color");
        for (int i = 1; i <= K; i++) {
            cvc5::DatatypeConstructorDecl c = tm.mkDatatypeConstructorDecl("C" + to_string(i));
            color_decl.addConstructor(c);
        }
        cvc5::Sort color_sort = tm.mkDatatypeSort(color_decl);
        cvc5::Datatype dt = color_sort.getDatatype();

        for (int i = 1; i <= K; i++) {
            cvc5::Term op = dt.getConstructor("C" + to_string(i)).getTerm();
            color_constants.push_back(tm.mkTerm(cvc5::Kind::APPLY_CONSTRUCTOR, {op}));
        }

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(color_sort, "node_" + to_string(i));
            cvc5::Term domain_constraint = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[0]});
            for (int c = 1; c < K; c++) {
                cvc5::Term is_color_c = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[c]});
                domain_constraint = tm.mkTerm(cvc5::Kind::OR, {domain_constraint, is_color_c});
            }
            solver.assertFormula(domain_constraint);
        }
    }
};

// ============================================================================
// 7. SIMPLE UNINTERPRETED FUNCTIONS
// ============================================================================
class UfColorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> color_constants;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_UF"); }
    void build_variables_and_bounds() override {
        cvc5::Sort color_sort = tm.mkUninterpretedSort("Color");
        for (int i = 1; i <= K; i++) {
            cvc5::Term color_const = tm.mkConst(color_sort, "C" + to_string(i));
            color_constants.push_back(color_const);
        }
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) {
                cvc5::Term eq = tm.mkTerm(cvc5::Kind::EQUAL, {color_constants[i], color_constants[j]});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT, {eq}));
            }
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(color_sort, "node_" + to_string(i));
            cvc5::Term domain_constraint = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[0]});
            for (int c = 1; c < K; c++) {
                cvc5::Term is_color_c = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[c]});
                domain_constraint = tm.mkTerm(cvc5::Kind::OR, {domain_constraint, is_color_c});
            }
            solver.assertFormula(domain_constraint);
        }
    }
};

// ============================================================================
// 8. THEORY OF STRINGS (Original OR-Disjunction)
// ============================================================================
class StringColorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> color_constants;
    string int_to_alpha(int n) {
        string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
        string result = "";
        while (n > 0) {
            n--;
            result = chars[n % 52] + result;
            n /= 52;
        }
        return result;
    }
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_S"); }
    void build_variables_and_bounds() override {
        cvc5::Sort str_sort = tm.getStringSort();
        for (int i = 1; i <= K; i++) {
            string color_name = int_to_alpha(i);
            cvc5::Term color_const = tm.mkString(color_name);
            color_constants.push_back(color_const);
        }
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) {
                cvc5::Term eq = tm.mkTerm(cvc5::Kind::EQUAL, {color_constants[i], color_constants[j]});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT, {eq}));
            }
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
            cvc5::Term domain_constraint = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[0]});
            for (int c = 1; c < K; c++) {
                cvc5::Term is_color_c = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[c]});
                domain_constraint = tm.mkTerm(cvc5::Kind::OR, {domain_constraint, is_color_c});
            }
            solver.assertFormula(domain_constraint);
        }
    }
};

// ============================================================================
// 9. THEORY OF STRINGS (Lexicographical Boundaries Cube)
// ============================================================================
class StringLexColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_SLIA"); }
    void build_variables_and_bounds() override {
        if (K > 50) {
            throw runtime_error("STR-LEX only supports K <= 50 due to ASCII printable contiguity.");
        }
        cvc5::Sort str_sort = tm.getStringSort();
        cvc5::Term len_one = tm.mkInteger(1);
        
        string start_char(1, 'A');
        string end_char(1, (char)('A' + K - 1));
        cvc5::Term start_term = tm.mkString(start_char);
        cvc5::Term end_term = tm.mkString(end_char);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
            
            cvc5::Term len = tm.mkTerm(cvc5::Kind::STRING_LENGTH, {node_vars[i]});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {len, len_one}));
            
            solver.assertFormula(tm.mkTerm(cvc5::Kind::STRING_LEQ, {start_term, node_vars[i]}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::STRING_LEQ, {node_vars[i], end_term}));
        }
    }
};

// ============================================================================
// 10. NEW: THEORY OF STRINGS (String-To-Int Projection Cube)
// ============================================================================
class StringIntColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_SLIA"); }
    void build_variables_and_bounds() override {
        cvc5::Sort str_sort = tm.getStringSort();
        cvc5::Term one = tm.mkInteger(1);
        cvc5::Term k_term = tm.mkInteger(K);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
            
            // Native String-to-Int Mapping!
            cvc5::Term node_as_int = tm.mkTerm(cvc5::Kind::STRING_TO_INT, {node_vars[i]});
            
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GEQ, {node_as_int, one}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {node_as_int, k_term}));

            // Force the canonical spelling (no leading zeros), otherwise "2" and "02"
            // would be two different colors with the same integer value.
            // str.from_int returns a String, so this is a String = String equality.
            cvc5::Term canonical = tm.mkTerm(cvc5::Kind::STRING_FROM_INT, {node_as_int});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], canonical}));
        }
    }
};

// ============================================================================
// 11. NEW: THEORY OF STRINGS (Native Regex Set Cube)
// ============================================================================
class StringRegexColorer : public AbstractGraphColorer {
private:
    string int_to_alpha(int n) {
        string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
        string result = "";
        while (n > 0) {
            n--;
            result = chars[n % 52] + result;
            n /= 52;
        }
        return result;
    }
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_S"); }
    void build_variables_and_bounds() override {
        cvc5::Sort str_sort = tm.getStringSort();
        
        // 1. Build the Regex options
        vector<cvc5::Term> regex_options;
        for (int i = 1; i <= K; i++) {
            string color_name = int_to_alpha(i);
            cvc5::Term str_const = tm.mkString(color_name);
            // Convert literal string to a regex match
            cvc5::Term str_re = tm.mkTerm(cvc5::Kind::STRING_TO_REGEXP, {str_const});
            regex_options.push_back(str_re);
        }
        
        // 2. Unite them into a single Regular Language set
        cvc5::Term re_union;
        if (K == 1) {
            re_union = regex_options[0];
        } else {
            re_union = tm.mkTerm(cvc5::Kind::REGEXP_UNION, regex_options);
        }

        // 3. Constrain nodes natively to the Regex Language!
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::STRING_IN_REGEXP, {node_vars[i], re_union}));
        }
    }
};

// ============================================================================
// THEORY OF STRINGS (Substrings of a word with exactly K distinct substrings)
// ============================================================================
#ifndef SUBSTRING_TABLE_PATH
#define SUBSTRING_TABLE_PATH "substring_strings.txt"
#endif

class StringSubstringColorer : public AbstractGraphColorer {
private:
    string word;

    // Looks K up in the table written by gen_substring_strings.py ("K string" per line).
    // Outside the table, 'a' repeated K-1 times has exactly K distinct substrings
    // ("", "a", ..., "a"*(K-1)).
    string find_word() {
        ifstream table(SUBSTRING_TABLE_PATH);
        if (!table.is_open()) {
            cerr << "Warning: could not open " << SUBSTRING_TABLE_PATH
                 << ", using the fallback string" << endl;
        }
        string line;
        while (getline(table, line)) {
            if (line.empty() || line[0] == '#') continue;
            stringstream ss(line);
            int k;
            string w; // stays empty for K = 1, whose only substring is ""
            ss >> k >> w;
            if (k == K) return w;
        }
        return string(K - 1, 'a');
    }
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_S"); }
    void build_variables_and_bounds() override {
        word = find_word();
        cvc5::Sort str_sort = tm.getStringSort();
        cvc5::Term word_term = tm.mkString(word);

        // Every node is one of the K distinct substrings of the word (the empty string included)
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::STRING_CONTAINS, {word_term, node_vars[i]}));
        }
    }
    void print_model() override {
        AbstractGraphColorer::print_model();
        cout << "word: \"" << word << "\"";
    }
};

// ============================================================================
// 12. NEW: THEORY OF FINITE SETS (Power Set Cube)
// ============================================================================
class SetColorer : public AbstractGraphColorer {
private:
    cvc5::Sort set_sort;
    cvc5::Term empty_set;

    // Helper to convert an integer 'n' into a unique Set using its binary bits.
    // e.g., n = 5 (binary 101) -> returns the set {0, 2}
    cvc5::Term build_set_from_int(int n) {
        vector<cvc5::Term> args;
        int bit_pos = 0;
        
        while (n > 0) {
            if (n % 2 == 1) {
                // Collect the raw elements, not singletons!
                args.push_back(tm.mkInteger(bit_pos));
            }
            n /= 2;
            bit_pos++;
        }
        
        // If the number is 0 (the empty set), just return it directly
        if (args.empty()) {
            return empty_set;
        }
        
        // SMT-LIB set.insert requires the base set to be the final argument
        args.push_back(empty_set);
        
        return tm.mkTerm(cvc5::Kind::SET_INSERT, args);
    }

public:
    using AbstractGraphColorer::AbstractGraphColorer;

protected:
    void configure_theory() override { 
        solver.setLogic("QF_FSLIA"); // Finite Sets + Integers for the elements
    }

    void build_variables_and_bounds() override {
        // 1. Calculate how many base elements (L) we need so that 2^L >= K
        int L = 0;
        while ((1 << L) < K) { L++; }

        // 2. Setup the Set Theory structures
        cvc5::Sort int_sort = tm.getIntegerSort();
        set_sort = tm.mkSetSort(int_sort);
        empty_set = tm.mkEmptySet(set_sort);

        // 3. Build the "Universe" Set: {0, 1, 2, ..., L-1}
        // This is represented by the integer where all L bits are 1
        cvc5::Term universe_set = build_set_from_int((1 << L) - 1);

        // 4. Pre-build the banned sets for when K is not a power of 2
        vector<cvc5::Term> banned_sets;
        for (int b = K; b < (1 << L); b++) {
            banned_sets.push_back(build_set_from_int(b));
        }

        // 5. Build node variables and apply constraints
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(set_sort, "node_" + to_string(i));
            
            // CONSTRAINT A: The node's color must be a SUBSET of the Universe
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_SUBSET, {node_vars[i], universe_set}));

            // CONSTRAINT B: Ban the excess sets (if K != 2^L)
            for (const auto& banned : banned_sets) {
                cvc5::Term eq_banned = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], banned});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT, {eq_banned}));
            }
        }
    }
};

// ============================================================================
// 14. THEORY OF ARRAYS (Explicit Array Chain - Sebastiani Encoding)
// ============================================================================
class ArrayExplicitColorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> i1_vars;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_ALIA"); }
    
    void build_variables_and_bounds() override {
        cvc5::Sort int_sort = tm.getIntegerSort();
        cvc5::Sort array_sort = tm.mkArraySort(int_sort, int_sort);
        
        i1_vars.resize(num_nodes + 1);

        for (int i = 1; i <= num_nodes; i++) {
            // The free index i_1 (acts as the color selector, completely unbounded)
            i1_vars[i] = tm.mkConst(int_sort, "i_1_" + to_string(i));
            
            // A_1 (The uninitialized base array)
            cvc5::Term current_A = tm.mkConst(array_sort, "A_1_" + to_string(i));
            
            // A_2 through A_{K+1}
            for(int j = 1; j <= K; j++) {
                cvc5::Term c_j = tm.mkInteger(j);
                // i_1 is the index for the first store; fixed distinct integers for the rest
                cvc5::Term index_j = (j == 1) ? i1_vars[i] : tm.mkInteger(j);
                
                cvc5::Term next_A = tm.mkConst(array_sort, "A_" + to_string(j+1) + "_" + to_string(i));
                cvc5::Term store_op = tm.mkTerm(cvc5::Kind::STORE, {current_A, index_j, c_j});
                
                // Assert A_{j+1} = A_j[ i_j -> c_j ]
                solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {next_A, store_op}));
                
                current_A = next_A;
            }
            
            // v_i = A_{K+1}[i_1]
            node_vars[i] = tm.mkTerm(cvc5::Kind::SELECT, {current_A, i1_vars[i]});
        }
    }
    
    void print_model() override {
        AbstractGraphColorer::print_model(); 
        for (int i = 1; i <= num_nodes; i++) {
            cout << "i_1_" << i << ": " << solver.getValue(i1_vars[i]).toString() << " ";
        }
    }
};

// ============================================================================
// 15. THEORY OF ARRAYS (Inline Array Chain - Sebastiani Encoding)
// ============================================================================
class ArrayInlineColorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> i1_vars;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_ALIA"); }
    
    void build_variables_and_bounds() override {
        cvc5::Sort int_sort = tm.getIntegerSort();
        cvc5::Sort array_sort = tm.mkArraySort(int_sort, int_sort);
        
        i1_vars.resize(num_nodes + 1);

        for (int i = 1; i <= num_nodes; i++) {
            // The free index i_1 (completely unbounded)
            i1_vars[i] = tm.mkConst(int_sort, "i_1_" + to_string(i));
            
            // A_1 (The uninitialized base array)
            cvc5::Term current_A = tm.mkConst(array_sort, "A_1_" + to_string(i));
            
            // Inline nested stores: store(store(store(A_1, ...)))
            for(int j = 1; j <= K; j++) {
                cvc5::Term c_j = tm.mkInteger(j);
                // i_1 is the index for the first store; fixed distinct integers for the rest
                cvc5::Term index_j = (j == 1) ? i1_vars[i] : tm.mkInteger(j);
                
                current_A = tm.mkTerm(cvc5::Kind::STORE, {current_A, index_j, c_j});
            }
            
            // v_i = A_{K+1}[i_1]
            node_vars[i] = tm.mkTerm(cvc5::Kind::SELECT, {current_A, i1_vars[i]});
        }
    }
    
    void print_model() override {
        AbstractGraphColorer::print_model(); 
        for (int i = 1; i <= num_nodes; i++) {
            cout << "i_1_" << i << ": " << solver.getValue(i1_vars[i]).toString() << " ";
        }
    }
};

// ============================================================================
// 16. THEORY OF ARRAYS (Global Mapped Index - The "Glorified LIA" Cube)
// ============================================================================
class ArrayMappedColorer : public AbstractGraphColorer {
private:
    cvc5::Term global_array;
    vector<cvc5::Term> idx_vars;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_ALIA"); }
    
    void build_variables_and_bounds() override {
        cvc5::Sort int_sort = tm.getIntegerSort();
        cvc5::Sort array_sort = tm.mkArraySort(int_sort, int_sort);
        
        // One single array for the entire graph
        global_array = tm.mkConst(array_sort, "GlobalColors");
        
        // Initialize the array mapping: A[c] = c for all c in 1..K
        for (int c = 1; c <= K; c++) {
            cvc5::Term c_term = tm.mkInteger(c);
            cvc5::Term read_c = tm.mkTerm(cvc5::Kind::SELECT, {global_array, c_term});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {read_c, c_term}));
        }
        
        cvc5::Term one = tm.mkInteger(1);
        cvc5::Term k_term = tm.mkInteger(K);
        idx_vars.resize(num_nodes + 1);

        for (int i = 1; i <= num_nodes; i++) {
            // The node's chosen index is bounded 1 <= idx <= K (Pure LIA logic)
            idx_vars[i] = tm.mkConst(int_sort, "idx_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GEQ, {idx_vars[i], one}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {idx_vars[i], k_term}));
            
            // The node's color is retrieved by passing the bounded index into the Array
            node_vars[i] = tm.mkTerm(cvc5::Kind::SELECT, {global_array, idx_vars[i]});
        }
    }
    
    void print_model() override {
        AbstractGraphColorer::print_model();
        for (int i = 1; i <= num_nodes; i++) {
            cout << "idx_" << i << ": " << solver.getValue(idx_vars[i]).toString() << " ";
        }
    }
};

// ============================================================================
// THEORY OF FINITE SETS (Element Membership Cube)
// ============================================================================
class SetMemberColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { 
        solver.setLogic("QF_FSLIA"); 
    }

    void build_variables_and_bounds() override {
        cvc5::Sort int_sort = tm.getIntegerSort();
        cvc5::Sort set_sort = tm.mkSetSort(int_sort);
        cvc5::Term empty_set = tm.mkEmptySet(set_sort);

        // 1. Build the domain set {1, 2, ..., K} using a flat SET_INSERT
        vector<cvc5::Term> args;
        for (int c = 1; c <= K; c++) {
            args.push_back(tm.mkInteger(c));
        }
        args.push_back(empty_set); // SMT-LIB requires the base set as the last argument
        
        cvc5::Term domain_set = tm.mkTerm(cvc5::Kind::SET_INSERT, args);

        // 2. Node variables are Integers, constrained by SET_MEMBER
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(int_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_MEMBER, {node_vars[i], domain_set}));
        }
    }
};

// ============================================================================
// THEORY OF FINITE SETS (Element Membership Cube - Bit-Vector)
// ============================================================================
class SetMemberBvColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { 
        // Enable all theories, as Sets + BV is a non-standard SMT-LIB combination
        solver.setLogic("ALL"); 
    }

    void build_variables_and_bounds() override {
        // 1. Calculate required bit-width for K
        int width = 1;
        while ((1 << width) - 1 < K) { width++; }

        cvc5::Sort bv_sort = tm.mkBitVectorSort(width);
        cvc5::Sort set_sort = tm.mkSetSort(bv_sort);
        cvc5::Term empty_set = tm.mkEmptySet(set_sort);

        // 2. Build the domain set using Bit-Vector constants
        vector<cvc5::Term> args;
        for (int c = 1; c <= K; c++) {
            args.push_back(tm.mkBitVector(width, c));
        }
        args.push_back(empty_set); // Base set goes last
        
        cvc5::Term domain_set = tm.mkTerm(cvc5::Kind::SET_INSERT, args);

        // 3. Node variables are Bit-Vectors, constrained by SET_MEMBER
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(bv_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_MEMBER, {node_vars[i], domain_set}));
        }
    }
};

// Same as SET-MEM-BV, but the elements are K constants of an uninterpreted sort.
// Unlike numerals, uninterpreted constants may be equal, so (distinct C1 ... CK) is asserted.
class SetMemberUfColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_UFFS"); }

    void build_variables_and_bounds() override {
        cvc5::Sort color_sort = tm.mkUninterpretedSort("Color");
        cvc5::Sort set_sort = tm.mkSetSort(color_sort);

        vector<cvc5::Term> colors;
        for (int c = 1; c <= K; c++) {
            colors.push_back(tm.mkConst(color_sort, "C" + to_string(c)));
        }
        if (K >= 2) {
            solver.assertFormula(tm.mkTerm(cvc5::Kind::DISTINCT, colors));
        }

        // The domain set {C1, ..., CK}
        vector<cvc5::Term> args = colors;
        args.push_back(tm.mkEmptySet(set_sort));
        cvc5::Term domain_set = tm.mkTerm(cvc5::Kind::SET_INSERT, args);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(color_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_MEMBER, {node_vars[i], domain_set}));
        }
    }
};

// ============================================================================
// 13. MAIN ENTRY POINT (ROUTER)
// ============================================================================
int main(int argc, char** argv) {
    bool produce_model = false;
    bool print_asserts = false;
    vector<string> pos_args;

    // Parse command line arguments
    for (int i = 1; i < argc; ++i) {
        string arg = argv[i];
        if (arg == "--help" || arg == "-h") {
            cout << "Usage: ./smt_solver_cvc5 <THEORY> <dimacs_file> <K> [OPTIONS]" << endl;
            cout << "Options:" << endl;
            cout << "  --model          Produce and print the coloring model if SAT" << endl;
            cout << "  --print-asserts  Print all asserted SMT formulas before solving" << endl;
            cout << "  --help, -h       Show this help message" << endl;
            cout << "\nAvailable Theories:" << endl;
            cout << "  LIA, IDL, BV, BV-ZERO, BV-AND, BV-ONEHOT, NLRA, NLRA-SIN, NLRA-COS, NLRA-SINCOS, NLRA-SINPI," << endl;
            cout << "  FF-PRIME, FF-POLY, FF-ROOTS, LIST-UF, LIST-DT, UF, STRING, STR-LEX, STR-INT, STR-REG, STR-SUB," << endl;
            cout << "  SET-CUBE, SET-MEM, SET-MEM-BV, SET-MEM-UF, ARR-EXP, ARR-INL, ARR-MAP" << endl;
            return 0;
        } else if (arg == "--model") {
            produce_model = true;
        } else if (arg == "--print-asserts") {
            print_asserts = true;
        } else {
            pos_args.push_back(arg);
        }
    }

    if (pos_args.size() < 3) {
        cerr << "Error: Missing required arguments." << endl;
        cerr << "Usage: ./smt_solver_cvc5 <THEORY> <dimacs_file> <K> [OPTIONS]" << endl;
        cerr << "Use --help for more information." << endl;
        return 1;
    }

    string theory = pos_args[0];
    string filename = pos_args[1];
    int K;
    
    try {
        K = stoi(pos_args[2]);
    } catch (...) {
        cerr << "Error: K must be an integer." << endl;
        return 1;
    }

    try {
        AbstractGraphColorer* colorer = nullptr;

        if (theory == "LIA") {
            colorer = new LiaColorer(K, produce_model, print_asserts);
        } else if (theory == "IDL") {
            colorer = new IdlColorer(K, produce_model, print_asserts);
        } else if (theory == "BV") {
            colorer = new BvColorer(K, produce_model, print_asserts);
        } else if (theory == "BV-ZERO") {
            colorer = new BvZeroColorer(K, produce_model, print_asserts);
        } else if (theory == "BV-AND") {
            colorer = new BvAndColorer(K, produce_model, print_asserts);
        } else if (theory == "BV-ONEHOT") {
            colorer = new BvOneHotColorer(K, produce_model, print_asserts);
        } else if (theory == "NLRA") {
            colorer = new NlraColorer(K, produce_model, print_asserts);
        } else if (theory == "NLRA-SIN") {
            colorer = new SinColorer(K, produce_model, print_asserts);
        } else if (theory == "NLRA-COS") {
            colorer = new CosColorer(K, produce_model, print_asserts);
        } else if (theory == "NLRA-SINCOS") {
            colorer = new SinCosColorer(K, produce_model, print_asserts);
        } else if (theory == "NLRA-SINPI") {
            colorer = new SinPiColorer(K, produce_model, print_asserts);
        } else if (theory == "FF-PRIME") {
            colorer = new FfPrimeColorer(K, produce_model, print_asserts);
        } else if (theory == "FF-POLY") {
            colorer = new FfPolyColorer(K, produce_model, print_asserts);
        } else if (theory == "FF-ROOTS") {
            colorer = new FfRootsColorer(K, produce_model, print_asserts);
        } else if (theory == "LIST-UF") {
            colorer = new ListUfColorer(K, produce_model, print_asserts);
        } else if (theory == "LIST-DT") {
            colorer = new ListDtColorer(K, produce_model, print_asserts);
        } else if (theory == "UF") {
            colorer = new UfColorer(K, produce_model, print_asserts);
        } else if (theory == "STRING") {
            colorer = new StringColorer(K, produce_model, print_asserts); 
        } else if (theory == "STR-LEX") {
            colorer = new StringLexColorer(K, produce_model, print_asserts); 
        } else if (theory == "STR-INT") {
            colorer = new StringIntColorer(K, produce_model, print_asserts); 
        } else if (theory == "STR-SUB") {
            colorer = new StringSubstringColorer(K, produce_model, print_asserts);
        } else if (theory == "STR-REG") {
            colorer = new StringRegexColorer(K, produce_model, print_asserts); 
        } else if (theory == "SET-CUBE") {
            colorer = new SetColorer(K, produce_model, print_asserts); 
        } else if (theory == "ARR-EXP") {
            colorer = new ArrayExplicitColorer(K, produce_model, print_asserts); 
        } else if (theory == "ARR-INL") {
            colorer = new ArrayInlineColorer(K, produce_model, print_asserts);
        } else if (theory == "ARR-MAP") {
            colorer = new ArrayMappedColorer(K, produce_model, print_asserts);\
        } else if (theory == "SET-MEM") {
            colorer = new SetMemberColorer(K, produce_model, print_asserts);
        } else if (theory == "SET-MEM-BV") {
            colorer = new SetMemberBvColorer(K, produce_model, print_asserts);
        } else if (theory == "SET-MEM-UF") {
            colorer = new SetMemberUfColorer(K, produce_model, print_asserts);
        } else {
            cerr << "Error: Unknown theory '" << theory << "'." << endl;
            return 1;
        }

        colorer->load_dimacs(filename);
        colorer->solve();

        delete colorer;
    } catch (const exception& e) {
        cerr << "Exception caught: " << e.what() << endl;
        return 1;
    }

    return 0;
}