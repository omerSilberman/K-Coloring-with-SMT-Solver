// Floating-point encoding: FP
#include "colorer.h"
#include "registry.h"

namespace {

// ============================================================================
// FLOATING POINT (the K floats right after 1.0)
// ============================================================================
// Float32 (8 exponent bits, 23 stored significand bits; cvc5's default FP solver
// only accepts Float32 and Float64). Between 1.0 and 2.0 the floats are 1 + m/2^23,
// one ulp apart, so 1.0 <= x <= 1 + (K-1)/2^23 holds exactly K floats: as reals the
// interval is a continuum, but only the K floats inside it exist.
// fp.leq is false on NaN and the bounds exclude +-0 and infinities, so fp.eq and
// = agree on the domain (outside it, NaN != NaN under fp.eq and +0 = -0).
class FpColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
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

}  // namespace

void register_fp(Cvc5Registry& registry) {
    registry.add("FP", make<FpColorer>());
}
