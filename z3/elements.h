// Element theories, shared by the theory-independent encodings (<ENCODING>-<ELEM>).
// The same idea as cvc5/elements.h: an encoding only needs some sort and n
// pairwise-distinct elements of it. Z3 has no finite fields, so there is no FF.
#pragma once

#include "colorer.h"

struct ElementDomain {
    z3::sort sort;
    vector<z3::expr> elements;     // pairwise distinct, given the constraints
    vector<z3::expr> constraints;  // to assert (e.g. distinct for uninterpreted constants)
};

class ElementTheory {
public:
    virtual ~ElementTheory() = default;
    // n pairwise-distinct elements of one sort
    virtual ElementDomain make_domain(z3::context& ctx, int n) = 0;
};

// Element theory by name (INT, REAL, BV, ...), or nullptr if unknown
unique_ptr<ElementTheory> make_element_theory(const string& name);
// The names make_element_theory knows, in --help order
const vector<string>& element_theory_names();

// Base for the theory-independent encodings: they take their elements from an
// ElementTheory and never look at what the elements are.
class ElementGenericColorer : public Z3Colorer {
protected:
    unique_ptr<ElementTheory> element_theory;
public:
    ElementGenericColorer(int k, bool model, bool print, unique_ptr<ElementTheory> elements)
        : Z3Colorer(k, model, print), element_theory(std::move(elements)) {}
protected:
    // Z3 picks the solver itself: most container/element combinations have no logic name
    void configure_theory() override { set_logic("ALL"); }
    // n distinct elements, with their side constraints asserted
    ElementDomain make_domain(int n) {
        ElementDomain domain = element_theory->make_domain(ctx, n);
        for (const auto& c : domain.constraints) solver.add(c);
        return domain;
    }
    // Z3 sets are arrays from the element sort to Bool
    z3::sort set_sort(const z3::sort& element_sort) { return ctx.array_sort(element_sort, ctx.bool_sort()); }
    // The set {elements...} of elements of element_sort
    z3::expr set_of(const vector<z3::expr>& elements, const z3::sort& element_sort) {
        z3::expr set = z3::empty_set(element_sort);
        for (const auto& e : elements) set = z3::set_add(set, e);
        return set;
    }
    // The set {base[j] | bit j of bits is 1}
    z3::expr set_of_bits(const vector<z3::expr>& base, int bits, const z3::sort& element_sort) {
        vector<z3::expr> members;
        for (int j = 0; j < (int)base.size(); j++) {
            if (bits >> j & 1) members.push_back(base[j]);
        }
        return set_of(members, element_sort);
    }
    // e in set (Z3's C++ set_member takes the element first)
    z3::expr member(const z3::expr& element, const z3::expr& set) { return z3::set_member(element, set); }
};
