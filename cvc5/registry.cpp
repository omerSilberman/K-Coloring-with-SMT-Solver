#include "registry.h"

#include <map>

void Registry::begin_group() {
    if (groups.empty() || !groups.back().empty()) groups.emplace_back();
}

void Registry::add(const string& name, Factory make) {
    if (groups.empty()) groups.emplace_back();
    groups.back().push_back({name, std::move(make)});
}

void Registry::add_generic(const string& name, const string& default_element, GenericFactory make) {
    generics.push_back({name, default_element, std::move(make)});
}

unique_ptr<AbstractGraphColorer> Registry::create(const string& theory, int K, bool model, bool print) const {
    for (const auto& group : groups) {
        for (const auto& encoding : group) {
            if (encoding.name == theory) return encoding.make(K, model, print);
        }
    }
    // Theory-independent: NAME (default element theory) or NAME-<ELEM>
    for (const auto& encoding : generics) {
        string element_name;
        if (theory == encoding.name) {
            element_name = encoding.default_element;
        } else if (theory.rfind(encoding.name + "-", 0) == 0) {
            element_name = theory.substr(encoding.name.size() + 1);
        } else {
            continue;
        }
        unique_ptr<ElementTheory> elements = make_element_theory(element_name);
        if (!elements) {
            throw runtime_error("Unknown element theory '" + element_name + "' in '" + theory + "'");
        }
        return encoding.make(K, model, print, std::move(elements));
    }
    return nullptr;
}

static string join(const vector<string>& items, const string& separator) {
    string out;
    for (size_t i = 0; i < items.size(); i++) out += (i ? separator : "") + items[i];
    return out;
}

void Registry::print_help(ostream& out) const {
    out << "\nAvailable Theories:" << endl;
    vector<string> lines;  // one per group that has theory-specific encodings
    for (const auto& group : groups) {
        vector<string> names;
        for (const auto& encoding : group) names.push_back(encoding.name);
        if (!names.empty()) lines.push_back(join(names, ", "));
    }
    for (size_t i = 0; i < lines.size(); i++) {
        out << "  " << lines[i] << (i + 1 < lines.size() ? "," : "") << endl;
    }

    vector<string> names;
    map<string, vector<string>> by_default;  // default element -> encodings
    for (const auto& encoding : generics) {
        names.push_back(encoding.name);
        by_default[encoding.default_element].push_back(encoding.name);
    }
    out << "\nTheory-independent encodings, as <ENCODING> or <ENCODING>-<ELEM>:" << endl;
    out << "  " << join(names, ", ") << endl;
    out << "  <ELEM> is the element theory: " << join(element_theory_names(), ", ") << endl;
    // e.g. "(default UF for OR and SEP, INT otherwise; ...)": the most common default is "otherwise"
    string usual;
    for (const auto& [element, users] : by_default) {
        if (usual.empty() || users.size() > by_default.at(usual).size()) usual = element;
    }
    vector<string> exceptions;
    for (const auto& [element, users] : by_default) {
        if (element != usual) exceptions.push_back(element + " for " + join(users, " and "));
    }
    exceptions.push_back(usual + " otherwise");
    out << "  (default " << join(exceptions, ", ") << "; BOOL has only 2 elements)" << endl;
}
