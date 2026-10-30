// Encodings by name. Each theory file adds its encodings in its register_* function;
// main.cpp calls those in a fixed order, which is also the order --help lists them in.
// (Explicit calls instead of self-registering static objects: static initialization
// order across files is unspecified, and --help, which the GUI reads, must be stable.)
#pragma once

#include <functional>

#include "colorer.h"
#include "elements.h"

class Registry {
public:
    using Factory = function<unique_ptr<AbstractGraphColorer>(int K, bool model, bool print)>;
    using GenericFactory = function<unique_ptr<AbstractGraphColorer>(
        int K, bool model, bool print, unique_ptr<ElementTheory> elements)>;

    // Starts a new line of names in --help (main.cpp calls it before each theory file)
    void begin_group();
    // A theory-specific encoding, e.g. "BV"
    void add(const string& name, Factory make);
    // A theory-independent encoding, run as NAME-<ELEM> or as NAME with default_element
    void add_generic(const string& name, const string& default_element, GenericFactory make);

    // The colorer for a theory name, or nullptr if the name is unknown.
    // Throws for a known encoding with an unknown element theory (e.g. SET-MASK-XYZ).
    unique_ptr<AbstractGraphColorer> create(const string& theory, int K, bool model, bool print) const;

    // The "Available Theories" and "Theory-independent encodings" parts of --help
    void print_help(ostream& out) const;

private:
    struct Specific { string name; Factory make; };
    struct Generic { string name; string default_element; GenericFactory make; };
    vector<vector<Specific>> groups;
    vector<Generic> generics;
};

// Factories for colorers whose constructor is (K, model, print, extra...) or
// (K, model, print, elements, extra...), e.g. make<BvOrderColorer>(true)
template <class Colorer, class... Extra>
Registry::Factory make(Extra... extra) {
    return [=](int k, bool model, bool print) -> unique_ptr<AbstractGraphColorer> {
        return make_unique<Colorer>(k, model, print, extra...);
    };
}
template <class Colorer, class... Extra>
Registry::GenericFactory make_generic(Extra... extra) {
    return [=](int k, bool model, bool print, unique_ptr<ElementTheory> elements) -> unique_ptr<AbstractGraphColorer> {
        return make_unique<Colorer>(k, model, print, std::move(elements), extra...);
    };
}

// One per theory file, in --help order
void register_int(Registry& registry);        // int.cpp
void register_bv(Registry& registry);         // bv.cpp
void register_fp(Registry& registry);         // fp.cpp
void register_real(Registry& registry);       // real.cpp
void register_ff(Registry& registry);         // ff.cpp
void register_uf(Registry& registry);         // uf.cpp
void register_datatypes(Registry& registry);  // datatypes.cpp
void register_bool(Registry& registry);       // bool.cpp
void register_strings(Registry& registry);    // strings.cpp
void register_sets(Registry& registry);       // sets.cpp
void register_arrays(Registry& registry);     // arrays.cpp
void register_sep(Registry& registry);        // sep.cpp
