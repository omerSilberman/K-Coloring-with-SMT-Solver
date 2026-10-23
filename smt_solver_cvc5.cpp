#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <stdexcept>
#include <memory>
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
    vector<pair<string, string>> cvc5_options;  // from --opt NAME=VALUE
    cvc5::TermManager tm; // CVC5 requires a TermManager
    cvc5::Solver solver;  // Native CVC5 Solver
    vector<cvc5::Term> node_vars;

public:
    AbstractGraphColorer(int k, bool model, bool print) 
        : K(k), produce_model(model), print_asserts(print), solver(tm) {
        if (produce_model) {
            solver.setOption("produce-models", "true");
        }
        solver.setOption("dag-thresh", "0");
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

    // cvc5 options to set before the encoding configures the solver
    void set_cvc5_options(const vector<pair<string, string>>& options) { cvc5_options = options; }

    void solve() {
        // Before configure_theory, so options an encoding requires (e.g. SEP's) still win
        for (const auto& [name, value] : cvc5_options) {
            solver.setOption(name, value);
        }
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
    // Override for encodings whose node color is not a single term in node_vars
    // (null term = nothing to assert for this edge)
    virtual cvc5::Term edge_constraint_between(int u, int v) {
        return edge_constraint(node_vars[u], node_vars[v]);
    }

private:
    void build_universal_edge_constraints() {
        for (const auto& edge : edges) {
            cvc5::Term constraint = edge_constraint_between(edge.first, edge.second);
            if (!constraint.isNull()) {
                solver.assertFormula(constraint);
            }
        }
    }
};

// ============================================================================
// ELEMENT THEORIES (shared by the theory-independent encodings)
// ============================================================================
// A theory-independent encoding (sets, arrays, ...) only needs some sort and n
// pairwise-distinct elements of it. Everything theory-specific lives here, so the
// encoding is written once and runs with any element theory: <ENCODING>-<ELEM>.
struct ElementDomain {
    cvc5::Sort sort;
    vector<cvc5::Term> elements;     // pairwise distinct, given the constraints
    vector<cvc5::Term> constraints;  // to assert (e.g. distinct for uninterpreted constants)
};

static bool is_prime(int n) {
    if (n < 2) return false;
    for (int d = 2; d * d <= n; d++) {
        if (n % d == 0) return false;
    }
    return true;
}

class ElementTheory {
public:
    virtual ~ElementTheory() = default;
    // n pairwise-distinct elements of one sort
    virtual ElementDomain make_domain(cvc5::TermManager& tm, int n) = 0;
    // This theory's part of an SMT-LIB logic name ("LIA", "BV", ...; "" for none)
    virtual string logic() const = 0;
};

// Integers 0, ..., n-1
class IntElements : public ElementTheory {
public:
    string logic() const override { return "LIA"; }
    ElementDomain make_domain(cvc5::TermManager& tm, int n) override {
        ElementDomain d{tm.getIntegerSort(), {}};
        for (int j = 0; j < n; j++) d.elements.push_back(tm.mkInteger(j));
        return d;
    }
};

// Reals 0, ..., n-1
class RealElements : public ElementTheory {
public:
    string logic() const override { return "LRA"; }
    ElementDomain make_domain(cvc5::TermManager& tm, int n) override {
        ElementDomain d{tm.getRealSort(), {}};
        for (int j = 0; j < n; j++) d.elements.push_back(tm.mkReal(j));
        return d;
    }
};

// Bit-vectors 0, ..., n-1 at the smallest width that holds n-1
class BvElements : public ElementTheory {
public:
    string logic() const override { return "BV"; }
    ElementDomain make_domain(cvc5::TermManager& tm, int n) override {
        int width = 1;
        while ((1 << width) < n) { width++; }
        ElementDomain d{tm.mkBitVectorSort(width), {}};
        for (int j = 0; j < n; j++) d.elements.push_back(tm.mkBitVector(width, j));
        return d;
    }
};

// String literals "0", ..., "n-1"
class StringElements : public ElementTheory {
public:
    string logic() const override { return "S"; }
    ElementDomain make_domain(cvc5::TermManager& tm, int n) override {
        ElementDomain d{tm.getStringSort(), {}};
        for (int j = 0; j < n; j++) d.elements.push_back(tm.mkString(to_string(j)));
        return d;
    }
};

// Constants E0, ..., E(n-1) of an uninterpreted sort, plus (distinct E0 ... E(n-1))
class UfElements : public ElementTheory {
public:
    string logic() const override { return "UF"; }
    ElementDomain make_domain(cvc5::TermManager& tm, int n) override {
        ElementDomain d{tm.mkUninterpretedSort("Elem"), {}};
        for (int j = 0; j < n; j++) d.elements.push_back(tm.mkConst(d.sort, "E" + to_string(j)));
        if (n >= 2) d.constraints.push_back(tm.mkTerm(cvc5::Kind::DISTINCT, d.elements));
        return d;
    }
};

// Enumeration datatype Elem = E0 | ... | E(n-1) (at least one constructor)
class DtElements : public ElementTheory {
public:
    string logic() const override { return "DT"; }
    ElementDomain make_domain(cvc5::TermManager& tm, int n) override {
        cvc5::DatatypeDecl decl = tm.mkDatatypeDecl("Elem");
        for (int j = 0; j < max(n, 1); j++) {
            cvc5::DatatypeConstructorDecl c = tm.mkDatatypeConstructorDecl("E" + to_string(j));
            decl.addConstructor(c);
        }
        ElementDomain d{tm.mkDatatypeSort(decl), {}};
        cvc5::Datatype dt = d.sort.getDatatype();
        for (int j = 0; j < n; j++) {
            cvc5::Term op = dt.getConstructor("E" + to_string(j)).getTerm();
            d.elements.push_back(tm.mkTerm(cvc5::Kind::APPLY_CONSTRUCTOR, {op}));
        }
        return d;
    }
};

// Elements 0, ..., n-1 of GF(p), p the smallest prime >= n (cvc5 built with --cocoa)
class FfElements : public ElementTheory {
public:
    string logic() const override { return "FF"; }
    ElementDomain make_domain(cvc5::TermManager& tm, int n) override {
        int p = max(n, 2);
        while (!is_prime(p)) { p++; }
        ElementDomain d{tm.mkFiniteFieldSort(to_string(p)), {}};
        for (int j = 0; j < n; j++) d.elements.push_back(tm.mkFiniteFieldElem(to_string(j), d.sort));
        return d;
    }
};

// The n Float32 values right after 1.0 (1 + j/2^23), as in the FP encoding.
// Sets compare elements with =, not fp.eq, so NaN and +-0 are not an issue.
class FpElements : public ElementTheory {
public:
    string logic() const override { return "FP"; }
    ElementDomain make_domain(cvc5::TermManager& tm, int n) override {
        const uint32_t exp_bits = 8, frac_bits = 23;
        uint32_t bias = (1u << (exp_bits - 1)) - 1;
        ElementDomain d{tm.mkFloatingPointSort(exp_bits, frac_bits + 1), {}};
        for (int j = 0; j < n; j++) {
            cvc5::Term bits = tm.mkBitVector(1 + exp_bits + frac_bits, (bias << frac_bits) | j);
            d.elements.push_back(tm.mkFloatingPoint(exp_bits, frac_bits + 1, bits));
        }
        return d;
    }
};

// false, true: only two elements exist
class BoolElements : public ElementTheory {
public:
    string logic() const override { return ""; }
    ElementDomain make_domain(cvc5::TermManager& tm, int n) override {
        if (n > 2) throw runtime_error("BOOL has only 2 elements (" + to_string(n) + " needed)");
        ElementDomain d{tm.getBooleanSort(), {}};
        for (int j = 0; j < n; j++) d.elements.push_back(tm.mkBoolean(j == 1));
        return d;
    }
};

// Element theory by name, or nullptr if unknown
static unique_ptr<ElementTheory> make_element_theory(const string& name) {
    if (name == "INT")  return make_unique<IntElements>();
    if (name == "REAL") return make_unique<RealElements>();
    if (name == "BV")   return make_unique<BvElements>();
    if (name == "STR")  return make_unique<StringElements>();
    if (name == "UF")   return make_unique<UfElements>();
    if (name == "DT")   return make_unique<DtElements>();
    if (name == "FF")   return make_unique<FfElements>();
    if (name == "FP")   return make_unique<FpElements>();
    if (name == "BOOL") return make_unique<BoolElements>();
    return nullptr;
}

// Base for the theory-independent encodings: they take their elements from an
// ElementTheory and never look at what the elements are.
class ElementGenericColorer : public AbstractGraphColorer {
protected:
    unique_ptr<ElementTheory> element_theory;
public:
    ElementGenericColorer(int k, bool model, bool print, unique_ptr<ElementTheory> elements)
        : AbstractGraphColorer(k, model, print), element_theory(std::move(elements)) {}
protected:
    // The encoding's own part of the logic name ("FS" for sets, "A" for arrays, ...)
    virtual string container_logic() const { return ""; }
    // QF_ + the container and element parts, e.g. QF_LIAFS for sets of integers.
    // cvc5 accepts the parts in any order.
    void configure_theory() override {
        string parts = container_logic() + element_theory->logic();
        solver.setLogic(parts.empty() ? "QF_UF" : "QF_" + parts);  // QF_UF: just Booleans
    }
    // n distinct elements, with their side constraints asserted
    ElementDomain make_domain(int n) {
        ElementDomain domain = element_theory->make_domain(tm, n);
        assert_constraints(domain);
        return domain;
    }
    void assert_constraints(const ElementDomain& domain) {
        for (const auto& c : domain.constraints) solver.assertFormula(c);
    }
    // The set {elements...} of sort set_sort
    cvc5::Term set_of(vector<cvc5::Term> elements, const cvc5::Sort& set_sort) {
        cvc5::Term empty = tm.mkEmptySet(set_sort);
        if (elements.empty()) return empty;
        elements.push_back(empty);  // SMT-LIB set.insert takes the base set last
        return tm.mkTerm(cvc5::Kind::SET_INSERT, elements);
    }
    // The set {base[j] | bit j of bits is 1}
    cvc5::Term set_of_bits(const vector<cvc5::Term>& base, int bits, const cvc5::Sort& set_sort) {
        vector<cvc5::Term> members;
        for (int j = 0; j < (int)base.size(); j++) {
            if (bits >> j & 1) members.push_back(base[j]);
        }
        return set_of(members, set_sort);
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
// INTEGERS MODULO K (an infinite domain folded onto K colors)
// ============================================================================
// Each node is an unbounded integer x, and its color is x mod K. Edges compare
// the residues, so the solver has to see past the infinitely many values of x.
class IntModColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
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
class IntPow2Colorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> exponents;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("ALL"); }
    void build_variables_and_bounds() override {
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
// BIT-VECTORS MODULO K (INT-MOD with bit-vectors)
// ============================================================================
// Each node is an unconstrained 32-bit vector x, and its color is x urem K. Edges
// compare the residues. Bit-vectors cannot be unbounded, so 32 bits stands in for
// "much wider than needed": 2^32 values fold onto K colors.
class BvModColorer : public AbstractGraphColorer {
private:
    static const int WIDTH = 32;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_BV"); }
    void build_variables_and_bounds() override {
        cvc5::Sort bv_sort = tm.mkBitVectorSort(WIDTH);
        for (int i = 1; i <= num_nodes; ++i) {
            node_vars[i] = tm.mkConst(bv_sort, "node_" + to_string(i));
        }
    }
    cvc5::Term residue(const cvc5::Term& x) {
        return tm.mkTerm(cvc5::Kind::BITVECTOR_UREM, {x, tm.mkBitVector(WIDTH, K)});
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
// FLOATING POINT (the K floats right after 1.0)
// ============================================================================
// Float32 (8 exponent bits, 23 stored significand bits; cvc5's default FP solver
// only accepts Float32 and Float64). Between 1.0 and 2.0 the floats are 1 + m/2^23,
// one ulp apart, so 1.0 <= x <= 1 + (K-1)/2^23 holds exactly K floats: as reals the
// interval is a continuum, but only the K floats inside it exist.
// fp.leq is false on NaN and the bounds exclude +-0 and infinities, so fp.eq and
// = agree on the domain (outside it, NaN != NaN under fp.eq and +0 = -0).
class FpColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_FP"); }
    void build_variables_and_bounds() override {
        const uint32_t exp_bits = 8, frac_bits = 23;
        if (K > (1 << frac_bits)) {
            throw runtime_error("FP only supports K <= 2^23");
        }
        // cvc5 counts the hidden bit in the significand width
        cvc5::Sort fp_sort = tm.mkFloatingPointSort(exp_bits, frac_bits + 1);
        uint32_t bias = (1u << (exp_bits - 1)) - 1;  // exponent field of 1.0
        auto float_with_fraction = [&](uint32_t m) {
            // sign 0 | exponent bias | fraction m
            cvc5::Term bits = tm.mkBitVector(1 + exp_bits + frac_bits, (bias << frac_bits) | m);
            return tm.mkFloatingPoint(exp_bits, frac_bits + 1, bits);
        };
        cvc5::Term lower = float_with_fraction(0);      // 1.0
        cvc5::Term upper = float_with_fraction(K - 1);  // 1 + (K-1)/2^23

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(fp_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::FLOATINGPOINT_LEQ, {lower, node_vars[i]}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::FLOATINGPOINT_LEQ, {node_vars[i], upper}));
        }
    }
    cvc5::Term edge_constraint(const cvc5::Term& u, const cvc5::Term& v) override {
        return tm.mkTerm(cvc5::Kind::NOT, {tm.mkTerm(cvc5::Kind::FLOATINGPOINT_EQ, {u, v})});
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
// FINITE FIELDS (GF(p), p prime - cvc5 needs to be built with --cocoa)
// ============================================================================
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

// Nullstellensatz coloring (Bayer; De Loera et al.): the same K-th roots of unity as
// FF-ROOTS, but every edge is an equation instead of a disequality:
//   u^(K-1) + u^(K-2) v + ... + v^(K-1) = 0
// The left side is (u^K - v^K) / (u - v). For u != v both K-th roots, u^K - v^K = 0
// and u - v != 0, so it is 0. For u = v it is K u^(K-1), which is not 0 because
// u != 0 and p does not divide K (p = 1 mod K). The whole problem becomes a system of
// polynomial equations, which cvc5 solves with Groebner bases.
class FfNullstellensatzColorer : public FfRootsColorer {
public:
    using FfRootsColorer::FfRootsColorer;
protected:
    cvc5::Term edge_constraint(const cvc5::Term& u, const cvc5::Term& v) override {
        // u_pows[j] = u^j, v_pows[j] = v^j for j = 0..K-1
        vector<cvc5::Term> u_pows = {ff_const(1)}, v_pows = {ff_const(1)};
        for (int j = 1; j < K; j++) {
            u_pows.push_back(j == 1 ? u : tm.mkTerm(cvc5::Kind::FINITE_FIELD_MULT, {u_pows[j - 1], u}));
            v_pows.push_back(j == 1 ? v : tm.mkTerm(cvc5::Kind::FINITE_FIELD_MULT, {v_pows[j - 1], v}));
        }
        vector<cvc5::Term> terms;
        for (int j = 0; j < K; j++) {
            terms.push_back(tm.mkTerm(cvc5::Kind::FINITE_FIELD_MULT, {u_pows[j], v_pows[K - 1 - j]}));
        }
        cvc5::Term sum = (K == 1) ? terms[0] : tm.mkTerm(cvc5::Kind::FINITE_FIELD_ADD, terms);
        return tm.mkTerm(cvc5::Kind::EQUAL, {sum, ff_const(0)});
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
// DATATYPES (Peano naturals)
// ============================================================================
// Nat = Z | S(pred: Nat), and the colors are Z, S(Z), ..., S^(K-1)(Z). Instead of
// listing them, each node gets one clause saying x is not K successors deep:
//   not (is-S(x) and is-S(pred x) and ... and is-S(pred^(K-1) x))
// Once some pred^j x is Z, the later pred applications are unconstrained, but the
// conjunction is already false at j, so the clause holds exactly for depth < K.
class PeanoColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_DT"); }
    void build_variables_and_bounds() override {
        cvc5::DatatypeDecl nat_decl = tm.mkDatatypeDecl("Nat");
        nat_decl.addConstructor(tm.mkDatatypeConstructorDecl("Z"));
        cvc5::DatatypeConstructorDecl succ = tm.mkDatatypeConstructorDecl("S");
        succ.addSelectorSelf("pred");
        nat_decl.addConstructor(succ);
        cvc5::Sort nat_sort = tm.mkDatatypeSort(nat_decl);
        cvc5::DatatypeConstructor s_cons = nat_sort.getDatatype().getConstructor("S");
        cvc5::Term is_s = s_cons.getTesterTerm();
        cvc5::Term pred = s_cons.getSelector("pred").getTerm();

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(nat_sort, "node_" + to_string(i));
            vector<cvc5::Term> deep;
            cvc5::Term current = node_vars[i];
            for (int j = 0; j < K; j++) {
                deep.push_back(tm.mkTerm(cvc5::Kind::APPLY_TESTER, {is_s, current}));
                current = tm.mkTerm(cvc5::Kind::APPLY_SELECTOR, {pred, current});
            }
            cvc5::Term too_deep = (K == 1) ? deep[0] : tm.mkTerm(cvc5::Kind::AND, deep);
            solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT, {too_deep}));
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
// PROPOSITIONAL LOGIC (The direct SAT encoding)
// ============================================================================
// K Booleans per node, c_i_j = "node i has color j", in logic QF_SAT (no theory):
//   at least one color:   c_i_1 or ... or c_i_K                  (one clause per node)
//   edges:                not c_u_j or not c_v_j                 (one clause per edge and color)
//   at most one (AMO):    not c_i_a or not c_i_b, for a < b      (only in BOOL-DIRECT-AMO)
// Without AMO a node may get several colors, but every one of them differs from all
// colors of its neighbours, so any one gives a valid coloring (the model takes the
// smallest). This is what BV-ONEHOT becomes after bit-blasting, minus the arithmetic.
class BoolDirectColorer : public AbstractGraphColorer {
private:
    bool at_most_one;
    vector<vector<cvc5::Term>> has_color;  // has_color[i][j-1] = c_i_j
public:
    BoolDirectColorer(int k, bool model, bool print, bool at_most_one)
        : AbstractGraphColorer(k, model, print), at_most_one(at_most_one) {}
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

// ============================================================================
// UNINTERPRETED SORT WITH A CARDINALITY CONSTRAINT
// ============================================================================
// Nodes are constants of an uninterpreted sort Color, edges are u != v, and the
// only other assertion is (_ fmf.card Color K): Color has at most K elements.
// There are no colors and no domain constraint: the sort's size is the domain.
// cvc5's cardinality solver (Reynolds et al.) keeps the equivalence classes of Color
// terms in "regions" of its disequality graph and must merge them down to at most K
// classes without merging two disequal terms - which is K-coloring the graph. It
// splits on merging two classes and reports a conflict when it finds a (K+1)-clique.
// (Its other modes, --uf-ss=no-minimal/none, only work with quantifier model finding
// and answer UNKNOWN here, so cvc5's default is used.)
class UfCardColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_UFC"); }  // C: cardinality constraints
    void build_variables_and_bounds() override {
        cvc5::Sort color_sort = tm.mkUninterpretedSort("Color");
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(color_sort, "node_" + to_string(i));
        }
        solver.assertFormula(tm.mkCardinalityConstraint(color_sort, K));
    }
};

// ============================================================================
// DISJUNCTION OVER K ELEMENTS (any element theory)
// ============================================================================
// x = e_1 or ... or e_K for K distinct elements. UF, STRING and LIST-DT are this
// encoding with a fixed element theory; OR-<ELEM> runs it with any.
class OrColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(domain.sort, "node_" + to_string(i));
            vector<cvc5::Term> choices;
            for (const auto& e : domain.elements) {
                choices.push_back(tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], e}));
            }
            solver.assertFormula((K == 1) ? choices[0] : tm.mkTerm(cvc5::Kind::OR, choices));
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
// 12. NEW: THEORY OF FINITE SETS (Power Set Cube, any element theory)
// ============================================================================
// x is a subset of U = {e_0, ..., e_(L-1)} with 2^L >= K, so bit j of the color
// is "e_j in x". The 2^L - K subsets for the colors K..2^L-1 are forbidden one by
// one with x != S.
class SetCubeColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    string container_logic() const override { return "FS"; }
    void build_variables_and_bounds() override {
        int L = 0;
        while ((1 << L) < K) { L++; }

        ElementDomain domain = make_domain(L);
        cvc5::Sort set_sort = tm.mkSetSort(domain.sort);
        cvc5::Term universe = set_of(domain.elements, set_sort);
        vector<cvc5::Term> banned_sets;
        for (int b = K; b < (1 << L); b++) {
            banned_sets.push_back(set_of_bits(domain.elements, b, set_sort));
        }

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(set_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_SUBSET, {node_vars[i], universe}));
            for (const auto& banned : banned_sets) {
                solver.assertFormula(tm.mkTerm(cvc5::Kind::DISTINCT, {node_vars[i], banned}));
            }
        }
    }
};

// ============================================================================
// 14-15. THEORY OF ARRAYS (Sebastiani array chain, any element theory)
// ============================================================================
// Indices and stored values are K distinct elements e_1..e_K:
//   A_{j+1} = store(A_j, i_j, e_j)   for j = 1..K, i_1 free and i_j = e_j otherwise
// and the node is A_{K+1}[i_1]: e_j if i_1 = e_j for some j >= 2, otherwise e_1
// (e_1 itself is a value of i_1 outside {e_2, ..., e_K}, so all K colors occur).
// ARR-EXP names every A_j with an explicit equation; ARR-INL nests the stores.
class ArrayChainColorer : public ElementGenericColorer {
private:
    bool inline_chain;
    vector<cvc5::Term> i1_vars;
public:
    ArrayChainColorer(int k, bool model, bool print, unique_ptr<ElementTheory> elements, bool inline_chain)
        : ElementGenericColorer(k, model, print, std::move(elements)), inline_chain(inline_chain) {}
protected:
    string container_logic() const override { return "A"; }
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        cvc5::Sort array_sort = tm.mkArraySort(domain.sort, domain.sort);
        i1_vars.resize(num_nodes + 1);

        for (int i = 1; i <= num_nodes; i++) {
            // The free index i_1 (acts as the color selector)
            i1_vars[i] = tm.mkConst(domain.sort, "i_1_" + to_string(i));
            // A_1 (the uninitialized base array)
            cvc5::Term current_A = tm.mkConst(array_sort, "A_1_" + to_string(i));

            for (int j = 1; j <= K; j++) {
                cvc5::Term index_j = (j == 1) ? i1_vars[i] : domain.elements[j - 1];
                cvc5::Term store_op = tm.mkTerm(cvc5::Kind::STORE, {current_A, index_j, domain.elements[j - 1]});
                if (inline_chain) {
                    current_A = store_op;
                } else {
                    // A_{j+1} = A_j[ i_j -> e_j ]
                    cvc5::Term next_A = tm.mkConst(array_sort, "A_" + to_string(j + 1) + "_" + to_string(i));
                    solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {next_A, store_op}));
                    current_A = next_A;
                }
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
// THEORY OF FINITE SETS (Element Membership Cube, any element theory)
// ============================================================================
// x in {e_1, ..., e_K}. SET-MEM-BV and SET-MEM-UF are SET-MEM-<ELEM> with BV and UF.
class SetMemberColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    string container_logic() const override { return "FS"; }
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        cvc5::Term domain_set = set_of(domain.elements, tm.mkSetSort(domain.sort));
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(domain.sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_MEMBER, {node_vars[i], domain_set}));
        }
    }
};

// ============================================================================
// THEORY OF FINITE SETS (Color classes instead of node colors, any element theory)
// ============================================================================
// The dual view: node i is the element id_i (n distinct elements), and there are
// K set variables S_1..S_K of node ids, one per color class.
//   partition:   S_1 u ... u S_K = {id_1, ..., id_n} and S_a n S_b = {} for a != b
//   independent: for every edge (u, v) and color c, not (id_u in S_c and id_v in S_c)
// There are no node variables at all; a node's color is the class it is in.
class SetClassesColorer : public ElementGenericColorer {
private:
    vector<cvc5::Term> node_ids;
    vector<cvc5::Term> classes;
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    string container_logic() const override { return "FS"; }
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(num_nodes);
        node_ids = domain.elements;
        cvc5::Sort set_sort = tm.mkSetSort(domain.sort);
        cvc5::Term empty_set = tm.mkEmptySet(set_sort);
        cvc5::Term all_nodes = set_of(node_ids, set_sort);

        for (int c = 1; c <= K; c++) {
            classes.push_back(tm.mkConst(set_sort, "S_" + to_string(c)));
        }
        cvc5::Term all_classes = classes[0];
        for (int c = 1; c < K; c++) {
            all_classes = tm.mkTerm(cvc5::Kind::SET_UNION, {all_classes, classes[c]});
        }
        solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {all_classes, all_nodes}));
        for (int a = 0; a < K; a++) {
            for (int b = a + 1; b < K; b++) {
                cvc5::Term overlap = tm.mkTerm(cvc5::Kind::SET_INTER, {classes[a], classes[b]});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {overlap, empty_set}));
            }
        }
    }
    cvc5::Term member(int node, int c) {
        return tm.mkTerm(cvc5::Kind::SET_MEMBER, {node_ids[node - 1], classes[c]});
    }
    cvc5::Term edge_constraint_between(int u, int v) override {
        vector<cvc5::Term> apart;
        for (int c = 0; c < K; c++) {
            apart.push_back(tm.mkTerm(cvc5::Kind::NOT,
                {tm.mkTerm(cvc5::Kind::AND, {member(u, c), member(v, c)})}));
        }
        return (K == 1) ? apart[0] : tm.mkTerm(cvc5::Kind::AND, apart);
    }
    void print_model() override {
        for (int i = 1; i <= num_nodes; i++) {
            int color = 0;
            for (int c = 0; c < K && color == 0; c++) {
                if (solver.getValue(member(i, c)).getBooleanValue()) color = c + 1;
            }
            cout << "node_" << i << ": " << color << " ";
        }
    }
};

// ============================================================================
// THEORY OF RELATIONS (The whole graph as one relational constraint, any element theory)
// ============================================================================
// Relations are sets of tuples. Nodes and colors are both named by elements: node i
// is id_i and color c is id_c, from max(n, K) distinct elements. E = {(u, v) | edge}
// is a constant, and the coloring is an unknown relation C between nodes and colors:
//   C subset Nodes x Colors       (Nodes = {(id_1), ..., (id_n)}, Colors = {(id_1), ..., (id_K)})
//   C join Colors = Nodes         (every node has at least one color)
//   (E join C) n C = {}           (the coloring constraint)
// E join C = {(u, c) | edge (u, v) and (v, c) in C}: the colors of u's neighbours.
// The last line says no node shares a color with a neighbour, for all edges at once.
// C does not have to be a function: if a node gets several colors, any one of them
// still gives a valid coloring, so a "functional" constraint would only add work.
class RelJoinColorer : public ElementGenericColorer {
private:
    vector<cvc5::Term> ids;
    cvc5::Term coloring;
    cvc5::Term pair(int a, int b) { return tm.mkTuple({ids[a - 1], ids[b - 1]}); }
    cvc5::Term relation(const vector<cvc5::Term>& tuples, const cvc5::Sort& sort) {
        return set_of(tuples, sort);
    }
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    // Tuples (relations) on top of sets have no SMT-LIB logic name
    void configure_theory() override { solver.setLogic("ALL"); }
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(max(num_nodes, K));
        ids = domain.elements;
        cvc5::Sort unary_sort = tm.mkSetSort(tm.mkTupleSort({domain.sort}));
        cvc5::Sort binary_sort = tm.mkSetSort(tm.mkTupleSort({domain.sort, domain.sort}));

        vector<cvc5::Term> node_tuples, color_tuples, edge_tuples;
        for (int i = 1; i <= num_nodes; i++) node_tuples.push_back(tm.mkTuple({ids[i - 1]}));
        for (int c = 1; c <= K; c++) color_tuples.push_back(tm.mkTuple({ids[c - 1]}));
        for (const auto& edge : edges) edge_tuples.push_back(pair(edge.first, edge.second));
        cvc5::Term nodes_rel = relation(node_tuples, unary_sort);
        cvc5::Term colors_rel = relation(color_tuples, unary_sort);
        cvc5::Term edges_rel = relation(edge_tuples, binary_sort);

        coloring = tm.mkConst(binary_sort, "C");
        cvc5::Term domain_rel = tm.mkTerm(cvc5::Kind::RELATION_PRODUCT, {nodes_rel, colors_rel});
        solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_SUBSET, {coloring, domain_rel}));
        cvc5::Term colored = tm.mkTerm(cvc5::Kind::RELATION_JOIN, {coloring, colors_rel});
        solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {colored, nodes_rel}));
        cvc5::Term neighbour_colors = tm.mkTerm(cvc5::Kind::RELATION_JOIN, {edges_rel, coloring});
        cvc5::Term clashes = tm.mkTerm(cvc5::Kind::SET_INTER, {neighbour_colors, coloring});
        solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {clashes, tm.mkEmptySet(binary_sort)}));
    }
    // All edges are in the single constraint above
    cvc5::Term edge_constraint_between(int, int) override { return cvc5::Term(); }
    void print_model() override {
        // A node's color is its smallest color in C
        for (int i = 1; i <= num_nodes; i++) {
            int color = 0;
            for (int c = 1; c <= K && color == 0; c++) {
                cvc5::Term has_c = tm.mkTerm(cvc5::Kind::SET_MEMBER, {pair(i, c), coloring});
                if (solver.getValue(has_c).getBooleanValue()) color = c;
            }
            cout << "node_" << i << ": " << color << " ";
        }
    }
};

// ============================================================================
// SEPARATION LOGIC (Colors are heap cells, any element theory)
// ============================================================================
// Locations and data both have the element sort; the data stored is the element
// e_1. The element theory is asked for K + 1 elements only so that the sort is known
// to hold K locations plus sep.nil, which is never allocated (the elements
// themselves are not used as locations).
// The heap is exactly K cells, c_1 |-> e_1 * ... * c_K |-> e_1, where * (separating
// conjunction) forces the cells to be distinct. Each node is a pointer into that
// heap: (x |-> e_1) * true. Edges are not disequalities but (u |-> e_1) * (v |-> e_1)
// * true: u and v point to two disjoint cells, which is the same thing as different colors.
class SepColorer : public ElementGenericColorer {
private:
    cvc5::Term data;
    cvc5::Term star(const vector<cvc5::Term>& parts) {
        return (parts.size() == 1) ? parts[0] : tm.mkTerm(cvc5::Kind::SEP_STAR, parts);
    }
    cvc5::Term points_to(const cvc5::Term& loc) {
        return tm.mkTerm(cvc5::Kind::SEP_PTO, {loc, data});
    }
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    void configure_theory() override {
        solver.setOption("incremental", "false");  // cvc5 requires this for separation logic
        solver.setLogic("ALL");
    }
    void build_variables_and_bounds() override {
        // The heap must be declared before the first assertion
        ElementDomain domain = element_theory->make_domain(tm, K + 1);
        solver.declareSepHeap(domain.sort, domain.sort);
        assert_constraints(domain);
        data = domain.elements[0];

        vector<cvc5::Term> cells;
        for (int c = 1; c <= K; c++) {
            cells.push_back(points_to(tm.mkConst(domain.sort, "c_" + to_string(c))));
        }
        solver.assertFormula(star(cells));

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(domain.sort, "node_" + to_string(i));
            solver.assertFormula(star({points_to(node_vars[i]), tm.mkTrue()}));
        }
    }
    cvc5::Term edge_constraint(const cvc5::Term& u, const cvc5::Term& v) override {
        return star({points_to(u), points_to(v), tm.mkTrue()});
    }
};

// ============================================================================
// THEORY OF FINITE SETS (Subset masks - BV-AND with sets, any element theory)
// ============================================================================
// BV-AND with each bit-vector replaced by a set: bit j of x is "e_j in x", for L
// distinct elements e_0..e_(L-1) of any element theory, with 2^L >= K.
//   x subset U, U = {e_0, ..., e_(L-1)}          (the 2^L subsets of U)
//   not (x subset A_b) for each 1-bit b of E      (E = 2^L - K values excluded)
// A_b is the set of a_b = (E with bits b..0 cleared) | (2^b - 1), the same maximal
// element as in BV-AND: "x is not a subset of A_b" is (x & ~a_b) != 0. So the
// excluded subsets are the ones of {0, ..., E-1}, and K = 2^L needs no A_b at all.
class SetMaskColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    string container_logic() const override { return "FS"; }
    void build_variables_and_bounds() override {
        int L = 0;
        while ((1 << L) < K) { L++; }
        int excluded = (1 << L) - K;

        ElementDomain domain = make_domain(L);
        cvc5::Sort set_sort = tm.mkSetSort(domain.sort);
        cvc5::Term universe = set_of(domain.elements, set_sort);
        vector<cvc5::Term> forbidden;  // the A_b
        for (int b = 0; b < L; b++) {
            if (excluded >> b & 1) {
                int maximal = ((excluded >> (b + 1)) << (b + 1)) | ((1 << b) - 1);
                forbidden.push_back(set_of_bits(domain.elements, maximal, set_sort));
            }
        }

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(set_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_SUBSET, {node_vars[i], universe}));
            for (const auto& a : forbidden) {
                solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT,
                    {tm.mkTerm(cvc5::Kind::SET_SUBSET, {node_vars[i], a})}));
            }
        }
    }
};

// ============================================================================
// THEORY-INDEPENDENT ENCODINGS (ROUTER)
// ============================================================================
// Each takes an element theory: <ENCODING>-<ELEM>, or just <ENCODING> for the
// default element theory (the one the encoding was first written with).
static const vector<pair<string, string>> GENERIC_ENCODINGS = {
    {"OR", "UF"}, {"SET-CUBE", "INT"}, {"SET-MASK", "INT"}, {"SET-MEM", "INT"},
    {"SET-CLASSES", "INT"}, {"REL-JOIN", "INT"}, {"ARR-EXP", "INT"}, {"ARR-INL", "INT"},
    {"SEP", "UF"},
};

// The colorer for a theory-independent encoding, or nullptr if theory is not one
static AbstractGraphColorer* make_generic_colorer(const string& theory, int K, bool model, bool print) {
    for (const auto& [encoding, default_element] : GENERIC_ENCODINGS) {
        string element_name;
        if (theory == encoding) {
            element_name = default_element;
        } else if (theory.rfind(encoding + "-", 0) == 0) {
            element_name = theory.substr(encoding.size() + 1);
        } else {
            continue;
        }
        unique_ptr<ElementTheory> elements = make_element_theory(element_name);
        if (!elements) {
            throw runtime_error("Unknown element theory '" + element_name + "' in '" + theory + "'");
        }
        if (encoding == "OR")          return new OrColorer(K, model, print, std::move(elements));
        if (encoding == "SET-CUBE")    return new SetCubeColorer(K, model, print, std::move(elements));
        if (encoding == "SET-MASK")    return new SetMaskColorer(K, model, print, std::move(elements));
        if (encoding == "SET-MEM")     return new SetMemberColorer(K, model, print, std::move(elements));
        if (encoding == "SET-CLASSES") return new SetClassesColorer(K, model, print, std::move(elements));
        if (encoding == "REL-JOIN")    return new RelJoinColorer(K, model, print, std::move(elements));
        if (encoding == "ARR-EXP")     return new ArrayChainColorer(K, model, print, std::move(elements), false);
        if (encoding == "ARR-INL")     return new ArrayChainColorer(K, model, print, std::move(elements), true);
        if (encoding == "SEP")         return new SepColorer(K, model, print, std::move(elements));
    }
    return nullptr;
}

// ============================================================================
// 13. MAIN ENTRY POINT (ROUTER)
// ============================================================================
int main(int argc, char** argv) {
    bool produce_model = false;
    bool print_asserts = false;
    vector<pair<string, string>> cvc5_options;
    vector<string> pos_args;

    // Parse command line arguments
    for (int i = 1; i < argc; ++i) {
        string arg = argv[i];
        if (arg == "--help" || arg == "-h") {
            cout << "Usage: ./smt_solver_cvc5 <THEORY> <dimacs_file> <K> [OPTIONS]" << endl;
            cout << "Options:" << endl;
            cout << "  --model          Produce and print the coloring model if SAT" << endl;
            cout << "  --print-asserts  Print all asserted SMT formulas before solving" << endl;
            cout << "  --opt NAME=VALUE Set a cvc5 option (repeatable), e.g. --opt bitblast=eager" << endl;
            cout << "                   (NAME alone means NAME=true)" << endl;
            cout << "  --help, -h       Show this help message" << endl;
            cout << "\nAvailable Theories:" << endl;
            cout << "  LIA, IDL, INT-MOD, INT-POW2, BV, BV-ZERO, BV-AND, BV-MOD, BV-ONEHOT, FP," << endl;
            cout << "  NLRA, NLRA-SQRT, NLRA-ROOTS, NLRA-SIN, NLRA-COS, NLRA-SINCOS, NLRA-SINPI," << endl;
            cout << "  FF-PRIME, FF-POLY, FF-ROOTS, FF-NULL, LIST-UF, LIST-DT, PEANO, UF, UF-CARD," << endl;
            cout << "  BOOL-DIRECT, BOOL-DIRECT-AMO," << endl;
            cout << "  STRING, STR-LEX, STR-INT, STR-REG, STR-SUB, ARR-MAP" << endl;
            cout << "\nTheory-independent encodings, as <ENCODING> or <ENCODING>-<ELEM>:" << endl;
            cout << "  OR, SET-CUBE, SET-MASK, SET-MEM, SET-CLASSES, REL-JOIN, ARR-EXP, ARR-INL, SEP" << endl;
            cout << "  <ELEM> is the element theory: INT, REAL, BV, STR, UF, DT, FF, FP, BOOL" << endl;
            cout << "  (default UF for OR and SEP, INT otherwise; BOOL has only 2 elements)" << endl;
            return 0;
        } else if (arg == "--model") {
            produce_model = true;
        } else if (arg == "--print-asserts") {
            print_asserts = true;
        } else if (arg == "--opt" || arg.rfind("--opt=", 0) == 0) {
            string option;
            if (arg == "--opt") {
                if (i + 1 >= argc) {
                    cerr << "Error: --opt needs NAME=VALUE." << endl;
                    return 1;
                }
                option = argv[++i];
            } else {
                option = arg.substr(6);
            }
            size_t eq = option.find('=');
            if (eq == 0 || option.empty()) {
                cerr << "Error: bad --opt '" << option << "', expected NAME=VALUE." << endl;
                return 1;
            }
            if (eq == string::npos) cvc5_options.push_back({option, "true"});
            else cvc5_options.push_back({option.substr(0, eq), option.substr(eq + 1)});
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
        AbstractGraphColorer* colorer = make_generic_colorer(theory, K, produce_model, print_asserts);

        if (colorer) {
            // theory-independent encoding
        } else if (theory == "LIA") {
            colorer = new LiaColorer(K, produce_model, print_asserts);
        } else if (theory == "IDL") {
            colorer = new IdlColorer(K, produce_model, print_asserts);
        } else if (theory == "INT-MOD") {
            colorer = new IntModColorer(K, produce_model, print_asserts);
        } else if (theory == "INT-POW2") {
            colorer = new IntPow2Colorer(K, produce_model, print_asserts);
        } else if (theory == "BV") {
            colorer = new BvColorer(K, produce_model, print_asserts);
        } else if (theory == "BV-ZERO") {
            colorer = new BvZeroColorer(K, produce_model, print_asserts);
        } else if (theory == "BV-AND") {
            colorer = new BvAndColorer(K, produce_model, print_asserts);
        } else if (theory == "BV-MOD") {
            colorer = new BvModColorer(K, produce_model, print_asserts);
        } else if (theory == "BV-ONEHOT") {
            colorer = new BvOneHotColorer(K, produce_model, print_asserts);
        } else if (theory == "FP") {
            colorer = new FpColorer(K, produce_model, print_asserts);
        } else if (theory == "NLRA") {
            colorer = new NlraColorer(K, produce_model, print_asserts);
        } else if (theory == "NLRA-SQRT") {
            colorer = new NlraSqrtColorer(K, produce_model, print_asserts);
        } else if (theory == "NLRA-ROOTS") {
            colorer = new NlraRootsColorer(K, produce_model, print_asserts);
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
        } else if (theory == "FF-NULL") {
            colorer = new FfNullstellensatzColorer(K, produce_model, print_asserts);
        } else if (theory == "LIST-UF") {
            colorer = new ListUfColorer(K, produce_model, print_asserts);
        } else if (theory == "LIST-DT") {
            colorer = new ListDtColorer(K, produce_model, print_asserts);
        } else if (theory == "PEANO") {
            colorer = new PeanoColorer(K, produce_model, print_asserts);
        } else if (theory == "BOOL-DIRECT") {
            colorer = new BoolDirectColorer(K, produce_model, print_asserts, false);
        } else if (theory == "BOOL-DIRECT-AMO") {
            colorer = new BoolDirectColorer(K, produce_model, print_asserts, true);
        } else if (theory == "UF-CARD") {
            colorer = new UfCardColorer(K, produce_model, print_asserts);
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
        } else if (theory == "ARR-MAP") {
            colorer = new ArrayMappedColorer(K, produce_model, print_asserts);
        } else {
            cerr << "Error: Unknown theory '" << theory << "'." << endl;
            return 1;
        }

        colorer->set_cvc5_options(cvc5_options);
        colorer->load_dimacs(filename);
        colorer->solve();

        delete colorer;
    } catch (const exception& e) {
        cerr << "Exception caught: " << e.what() << endl;
        return 1;
    }

    return 0;
}