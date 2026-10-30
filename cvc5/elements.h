// Element theories, shared by the theory-independent encodings (<ENCODING>-<ELEM>).
#pragma once

#include "colorer.h"

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

class ElementTheory {
public:
    virtual ~ElementTheory() = default;
    // n pairwise-distinct elements of one sort
    virtual ElementDomain make_domain(cvc5::TermManager& tm, int n) = 0;
    // This theory's part of an SMT-LIB logic name ("LIA", "BV", ...; "" for none)
    virtual string logic() const = 0;
};

// Element theory by name (INT, REAL, BV, ...), or nullptr if unknown
unique_ptr<ElementTheory> make_element_theory(const string& name);
// The names make_element_theory knows, in --help order
const vector<string>& element_theory_names();

// Base for the theory-independent encodings: they take their elements from an
// ElementTheory and never look at what the elements are.
class ElementGenericColorer : public Cvc5Colorer {
protected:
    unique_ptr<ElementTheory> element_theory;
public:
    ElementGenericColorer(int k, bool model, bool print, unique_ptr<ElementTheory> elements)
        : Cvc5Colorer(k, model, print), element_theory(std::move(elements)) {}
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
