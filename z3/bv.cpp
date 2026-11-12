// Bit-vector encodings: BV, BV-ZERO, BV-AND, BV-MOD, BV-ONEHOT, BV-ORDER, BV-ORDER-SHIFT
// (see cvc5/bv.cpp and the README for how each domain constraint works)
#include "colorer.h"
#include "registry.h"

namespace {

// Colors 1..K: 1 <=u x <=u K at the smallest width that holds K; when K = 2^w (K >= 2),
// width w and no bounds
class BvColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("QF_BV"); }
    void build_variables_and_bounds() override {
        if (strategies_given()) {
            // colors 0..K-1 at width w when K = 2^w (K >= 2), otherwise 1..K
            if (K >= 2 && (K & (K - 1)) == 0) {
                int w = 0;
                while ((1 << w) < K) { w++; }
                for (int c = 0; c < K; c++) colors.push_back(ctx.bv_val(c, w));
            } else {
                int w = 1;
                while ((1 << w) - 1 < K) { w++; }
                for (int c = 1; c <= K; c++) colors.push_back(ctx.bv_val(c, w));
            }
        }
        if (K >= 2 && (K & (K - 1)) == 0) {
            int width = 0;
            while ((1 << width) < K) { width++; }
            for (int i = 1; i <= num_nodes; i++) {
                node_vars[i] = constant("node_" + to_string(i), ctx.bv_sort(width));
            }
            return;
        }

        int width = 1;
        while ((1 << width) - 1 < K) { width++; }
        z3::expr one = ctx.bv_val(1, width), k_term = ctx.bv_val(K, width);
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.bv_sort(width));
            solver.add(z3::uge(node_vars[i], one));
            solver.add(z3::ule(node_vars[i], k_term));
        }
    }
};

// Colors 0..K-1: x <=u K-1, no bound when K = 2^w (K >= 2)
class BvZeroColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("QF_BV"); }
    void build_variables_and_bounds() override {
        int width = 1;
        while ((1 << width) < K) { width++; }
        bool needs_bound = (1 << width) != K;
        if (strategies_given()) {
            for (int c = 0; c < K; c++) colors.push_back(ctx.bv_val(c, width));
        }
        z3::expr max_term = ctx.bv_val(K - 1, width);
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.bv_sort(width));
            if (needs_bound) solver.add(z3::ule(node_vars[i], max_term));
        }
    }
};

// One literal (x & ~a_b) != 0 per 1-bit b of E = 2^w - K, excluding {0, ..., E-1}
class BvAndColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("QF_BV"); }
    void build_variables_and_bounds() override {
        int width = 1;
        while ((1 << width) < K) { width++; }
        int full = (1 << width) - 1;
        int excluded = (1 << width) - K;
        if (strategies_given()) {
            for (int c = 0; c < K; c++) colors.push_back(ctx.bv_val(excluded + c, width));  // E..2^w-1
        }

        z3::expr zero = ctx.bv_val(0, width);
        vector<z3::expr> masks;
        for (int b = 0; b < width; b++) {
            if (excluded >> b & 1) {
                int maximal = ((excluded >> (b + 1)) << (b + 1)) | ((1 << b) - 1);
                masks.push_back(ctx.bv_val(full & ~maximal, width));
            }
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.bv_sort(width));
            for (const auto& mask : masks) solver.add((node_vars[i] & mask) != zero);
        }
    }
};

// Unconstrained 32-bit x, color x urem K
class BvModColorer : public Z3Colorer {
private:
    static const int WIDTH = 32;
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
    // the colors are the residues 0..K-1
    void fix_color(int node, int color) override { solver.add(residue(node_vars[node]) == ctx.bv_val(color, WIDTH)); }
    string color_value(int color) override { return ctx.bv_val(color, WIDTH).to_string(); }
protected:
    void configure_theory() override { set_logic("QF_BV"); }
    void build_variables_and_bounds() override {
        for (int i = 1; i <= num_nodes; ++i) {
            node_vars[i] = constant("node_" + to_string(i), ctx.bv_sort(WIDTH));
        }
    }
    z3::expr residue(const z3::expr& x) { return z3::urem(x, ctx.bv_val(K, WIDTH)); }
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

// Width K, one bit set: x != 0 and (x & (x - 1)) = 0; edges (u & v) = 0
class BvOneHotColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    // A bit-vector constant from a binary string, most significant bit first (any width)
    z3::expr bits_value(const string& bits) {
        vector<bool> b;
        for (auto it = bits.rbegin(); it != bits.rend(); ++it) b.push_back(*it == '1');
        unique_ptr<bool[]> raw(new bool[b.size()]);
        for (size_t i = 0; i < b.size(); i++) raw[i] = b[i];
        return ctx.bv_val((unsigned)b.size(), raw.get());
    }
    void configure_theory() override { set_logic("QF_BV"); }
    void build_variables_and_bounds() override {
        if (strategies_given()) {
            for (int c = 0; c < K; c++) {
                string bits(K, '0');
                bits[K - 1 - c] = '1';  // only bit c
                colors.push_back(bits_value(bits));
            }
        }
        z3::expr zero = ctx.bv_val(0, K), one = ctx.bv_val(1, K);
        for (int i = 1; i <= num_nodes; i++) {
            z3::expr x = constant("node_" + to_string(i), ctx.bv_sort(K));
            node_vars[i] = x;
            solver.add(x != zero);
            solver.add((x & (x - one)) == zero);
        }
    }
    z3::expr edge_constraint(const z3::expr& u, const z3::expr& v) override {
        return (u & v) == ctx.bv_val(0, K);
    }
};

// Order (thermometer) encoding, width K-1: (x & (x + 1)) = 0, or with use_shift
// ((x >> 1) & ~x) = 0. With K = 1, x is 1 bit fixed to 0.
class BvOrderColorer : public Z3Colorer {
private:
    bool use_shift;
public:
    BvOrderColorer(int k, bool model, bool print, bool use_shift)
        : Z3Colorer(k, model, print), use_shift(use_shift) {}
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("QF_BV"); }
    void build_variables_and_bounds() override {
        int width = max(K - 1, 1);
        if (strategies_given()) {
            for (int c = 0; c < K; c++) {
                unique_ptr<bool[]> raw(new bool[width]);
                for (int b = 0; b < width; b++) raw[b] = b < c;  // the lowest c bits
                colors.push_back(ctx.bv_val((unsigned)width, raw.get()));
            }
        }
        z3::expr zero = ctx.bv_val(0, width), one = ctx.bv_val(1, width);
        for (int i = 1; i <= num_nodes; i++) {
            z3::expr x = constant("node_" + to_string(i), ctx.bv_sort(width));
            node_vars[i] = x;
            if (K == 1) {
                solver.add(x == zero);
                continue;
            }
            z3::expr bad = use_shift ? (z3::lshr(x, one) & ~x) : (x & (x + one));
            solver.add(bad == zero);
        }
    }
};

}  // namespace

void register_bv(Z3Registry& registry) {
    registry.add("BV", make<BvColorer>());
    registry.add("BV-ZERO", make<BvZeroColorer>());
    registry.add("BV-AND", make<BvAndColorer>());
    registry.add("BV-MOD", make<BvModColorer>());
    registry.add("BV-ONEHOT", make<BvOneHotColorer>());
    registry.add("BV-ORDER", make<BvOrderColorer>(false));
    registry.add("BV-ORDER-SHIFT", make<BvOrderColorer>(true));
}
