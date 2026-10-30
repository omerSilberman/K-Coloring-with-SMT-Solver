// Finite-field encodings: FF-PRIME, FF-POLY, FF-ROOTS, FF-NULL (cvc5 needs to be built with CoCoA)
#include "colorer.h"
#include "../common/util.h"
#include "registry.h"

namespace {

// ============================================================================
// FINITE FIELDS (GF(p), p prime - cvc5 needs to be built with --cocoa)
// ============================================================================
class FiniteFieldColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
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

}  // namespace

void register_ff(Cvc5Registry& registry) {
    registry.add("FF-PRIME", make<FfPrimeColorer>());
    registry.add("FF-POLY", make<FfPolyColorer>());
    registry.add("FF-ROOTS", make<FfRootsColorer>());
    registry.add("FF-NULL", make<FfNullstellensatzColorer>());
}
