// Bit-vector encodings: BV, BV-ZERO, BV-AND, BV-MOD, BV-ONEHOT, BV-ORDER, BV-ORDER-SHIFT
#include "colorer.h"
#include "registry.h"

namespace {

// ============================================================================
// BIT-VECTOR (BV)
// ============================================================================
// Colors 1..K: 1 <=u x <=u K, at the smallest width that holds K.
// When K = 2^w (K >= 2) the sort has exactly K values, so width w and no bounds.
class BvColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
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
class BvZeroColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
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
class BvAndColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
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
class BvModColorer : public Cvc5Colorer {
private:
    static const int WIDTH = 32;
public:
    using Cvc5Colorer::Cvc5Colorer;
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
class BvOneHotColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
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
// BIT-VECTOR (Order / "thermometer" encoding)
// ============================================================================
// Width K-1, and color c is the vector with its lowest c bits set (c = 0..K-1):
//   000, 001, 011, 111   for K = 4
// These are exactly the x with no 1 above a 0, stated two ways:
//   BV-ORDER:        (x & (x + 1)) = 0      x + 1 is a power of 2 (or wraps to 0 for 1...1)
//   BV-ORDER-SHIFT:  ((x >> 1) & ~x) = 0    bit b+1 set implies bit b set (no adder)
// Edges stay u != v. With K = 1 the width would be 0, so x is 1 bit fixed to 0.
class BvOrderColorer : public Cvc5Colorer {
private:
    bool use_shift;
public:
    BvOrderColorer(int k, bool model, bool print, bool use_shift)
        : Cvc5Colorer(k, model, print), use_shift(use_shift) {}
protected:
    void configure_theory() override { solver.setLogic("QF_BV"); }
    void build_variables_and_bounds() override {
        int width = max(K - 1, 1);
        cvc5::Sort bv_sort = tm.mkBitVectorSort(width);
        cvc5::Term zero = tm.mkBitVector(width, 0), one = tm.mkBitVector(width, 1);
        for (int i = 1; i <= num_nodes; i++) {
            cvc5::Term x = tm.mkConst(bv_sort, "node_" + to_string(i));
            node_vars[i] = x;
            if (K == 1) {
                solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {x, zero}));
                continue;
            }
            cvc5::Term bad;
            if (use_shift) {
                cvc5::Term above = tm.mkTerm(cvc5::Kind::BITVECTOR_LSHR, {x, one});
                bad = tm.mkTerm(cvc5::Kind::BITVECTOR_AND, {above, tm.mkTerm(cvc5::Kind::BITVECTOR_NOT, {x})});
            } else {
                cvc5::Term next = tm.mkTerm(cvc5::Kind::BITVECTOR_ADD, {x, one});
                bad = tm.mkTerm(cvc5::Kind::BITVECTOR_AND, {x, next});
            }
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {bad, zero}));
        }
    }
};

}  // namespace

void register_bv(Cvc5Registry& registry) {
    registry.add("BV", make<BvColorer>());
    registry.add("BV-ZERO", make<BvZeroColorer>());
    registry.add("BV-AND", make<BvAndColorer>());
    registry.add("BV-MOD", make<BvModColorer>());
    registry.add("BV-ONEHOT", make<BvOneHotColorer>());
    registry.add("BV-ORDER", make<BvOrderColorer>(false));
    registry.add("BV-ORDER-SHIFT", make<BvOrderColorer>(true));
}
