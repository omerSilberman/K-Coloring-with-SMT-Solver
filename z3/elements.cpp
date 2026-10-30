// The element theories: what INT, REAL, BV, ... mean in <ENCODING>-<ELEM>
// (the same elements as cvc5/elements.cpp).
#include "elements.h"

namespace {

// Integers 0, ..., n-1
class IntElements : public ElementTheory {
public:
    ElementDomain make_domain(z3::context& ctx, int n) override {
        ElementDomain d{ctx.int_sort(), {}, {}};
        for (int j = 0; j < n; j++) d.elements.push_back(ctx.int_val(j));
        return d;
    }
};

// Reals 0, ..., n-1
class RealElements : public ElementTheory {
public:
    ElementDomain make_domain(z3::context& ctx, int n) override {
        ElementDomain d{ctx.real_sort(), {}, {}};
        for (int j = 0; j < n; j++) d.elements.push_back(ctx.real_val(j));
        return d;
    }
};

// Bit-vectors 0, ..., n-1 at the smallest width that holds n-1
class BvElements : public ElementTheory {
public:
    ElementDomain make_domain(z3::context& ctx, int n) override {
        int width = 1;
        while ((1 << width) < n) { width++; }
        ElementDomain d{ctx.bv_sort(width), {}, {}};
        for (int j = 0; j < n; j++) d.elements.push_back(ctx.bv_val(j, width));
        return d;
    }
};

// String literals "0", ..., "n-1"
class StringElements : public ElementTheory {
public:
    ElementDomain make_domain(z3::context& ctx, int n) override {
        ElementDomain d{ctx.string_sort(), {}, {}};
        for (int j = 0; j < n; j++) d.elements.push_back(ctx.string_val(to_string(j)));
        return d;
    }
};

// Constants E0, ..., E(n-1) of an uninterpreted sort, plus (distinct E0 ... E(n-1))
class UfElements : public ElementTheory {
public:
    ElementDomain make_domain(z3::context& ctx, int n) override {
        ElementDomain d{ctx.uninterpreted_sort("Elem"), {}, {}};
        for (int j = 0; j < n; j++) d.elements.push_back(ctx.constant(("E" + to_string(j)).c_str(), d.sort));
        if (n >= 2) {
            z3::expr_vector all(ctx);
            for (const auto& e : d.elements) all.push_back(e);
            d.constraints.push_back(z3::distinct(all));
        }
        return d;
    }
};

// Enumeration datatype Elem = E0 | ... | E(n-1) (at least one constructor)
class DtElements : public ElementTheory {
public:
    ElementDomain make_domain(z3::context& ctx, int n) override {
        vector<string> names;
        for (int j = 0; j < max(n, 1); j++) names.push_back("E" + to_string(j));
        vector<const char*> c_names;
        for (const auto& name : names) c_names.push_back(name.c_str());
        z3::func_decl_vector constructors(ctx), testers(ctx);
        ElementDomain d{ctx.enumeration_sort("Elem", c_names.size(), c_names.data(), constructors, testers), {}, {}};
        for (int j = 0; j < n; j++) d.elements.push_back(constructors[j]());
        return d;
    }
};

// The n Float32 values right after 1.0 (1 + j/2^23), as in the FP encoding.
// Sets compare elements with =, not fp.eq, so NaN and +-0 are not an issue.
class FpElements : public ElementTheory {
public:
    ElementDomain make_domain(z3::context& ctx, int n) override {
        const unsigned exp_bits = 8, frac_bits = 23;
        unsigned bias = (1u << (exp_bits - 1)) - 1;
        ElementDomain d{ctx.fpa_sort(exp_bits, frac_bits + 1), {}, {}};
        for (int j = 0; j < n; j++) {
            d.elements.push_back(z3::fpa_fp(ctx.bv_val(0, 1), ctx.bv_val(bias, exp_bits), ctx.bv_val(j, frac_bits)));
        }
        return d;
    }
};

// false, true: only two elements exist
class BoolElements : public ElementTheory {
public:
    ElementDomain make_domain(z3::context& ctx, int n) override {
        if (n > 2) throw runtime_error("BOOL has only 2 elements (" + to_string(n) + " needed)");
        ElementDomain d{ctx.bool_sort(), {}, {}};
        for (int j = 0; j < n; j++) d.elements.push_back(ctx.bool_val(j == 1));
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
    if (name == "FP")   return make_unique<FpElements>();
    if (name == "BOOL") return make_unique<BoolElements>();
    if (name == "FF") throw runtime_error("Z3 has no finite fields (FF elements need cvc5)");
    return nullptr;
}

const vector<string>& element_theory_names() {
    static const vector<string> names = {"INT", "REAL", "BV", "STR", "UF", "DT", "FP", "BOOL"};
    return names;
}
