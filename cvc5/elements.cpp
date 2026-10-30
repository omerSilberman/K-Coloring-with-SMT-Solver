// The element theories: what INT, REAL, BV, ... mean in <ENCODING>-<ELEM>.
#include "elements.h"
#include "../common/util.h"

namespace {

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

}  // namespace

unique_ptr<ElementTheory> make_element_theory(const string& name) {
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

const vector<string>& element_theory_names() {
    static const vector<string> names = {"INT", "REAL", "BV", "STR", "UF", "DT", "FF", "FP", "BOOL"};
    return names;
}
