// Floating-point encoding: FP (see cvc5/fp.cpp and the README)
#include "colorer.h"
#include "registry.h"

namespace {

// The K Float32 values from 1.0 to 1 + (K-1)/2^23: 1.0 <= x <= 1 + (K-1)*2^-23,
// and edges use fp.eq
class FpColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_FP"); }
    void build_variables_and_bounds() override {
        const unsigned exp_bits = 8, frac_bits = 23;
        if (K > (1 << frac_bits)) {
            throw runtime_error("FP only supports K <= 2^23");
        }
        // Z3, like cvc5, counts the hidden bit in the significand width
        z3::sort fp_sort = ctx.fpa_sort(exp_bits, frac_bits + 1);
        unsigned bias = (1u << (exp_bits - 1)) - 1;  // exponent field of 1.0
        auto float_with_fraction = [&](unsigned m) {
            // sign 0 | exponent bias | fraction m
            return z3::fpa_fp(ctx.bv_val(0, 1), ctx.bv_val(bias, exp_bits), ctx.bv_val(m, frac_bits));
        };
        z3::expr lower = float_with_fraction(0);      // 1.0
        z3::expr upper = float_with_fraction(K - 1);  // 1 + (K-1)/2^23

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), fp_sort);
            solver.add(lower <= node_vars[i]);  // fp.leq
            solver.add(node_vars[i] <= upper);
        }
    }
    z3::expr edge_constraint(const z3::expr& u, const z3::expr& v) override {
        return !z3::fp_eq(u, v);
    }
};

}  // namespace

void register_fp(Z3Registry& registry) {
    registry.add("FP", make<FpColorer>());
}
