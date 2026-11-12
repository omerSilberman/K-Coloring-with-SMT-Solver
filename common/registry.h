// Encodings by name, for any engine. Each theory file adds its encodings in its
// register_* function; the engine's main.cpp calls those in a fixed order, which is also
// the order --help lists them in. (Explicit calls instead of self-registering static
// objects: static initialization order across files is unspecified, and --help, which
// the GUI reads, must be stable.)
#pragma once

#include <functional>
#include <map>
#include <stdexcept>

#include "colorer.h"
#include "json.h"

// Colorer: the engine's base class. Elements: its element-theory class, used by the
// theory-independent encodings (NAME-<ELEM>).
template <class Colorer, class Elements>
class Registry {
public:
    using Factory = function<unique_ptr<Colorer>(int K, bool model, bool print)>;
    using GenericFactory = function<unique_ptr<Colorer>(int K, bool model, bool print, unique_ptr<Elements>)>;
    using ElementFactory = function<unique_ptr<Elements>(const string& name)>;

    // make_elements: element theory by name (nullptr if unknown); element_names in --help order
    Registry(ElementFactory make_elements, vector<string> element_names)
        : make_elements(std::move(make_elements)), element_names(std::move(element_names)) {}

    // Starts a new line of names in --help (main.cpp calls it before each theory file)
    void begin_group() {
        if (groups.empty() || !groups.back().empty()) groups.emplace_back();
    }
    // A theory-specific encoding, e.g. "BV"
    void add(const string& name, Factory make) {
        if (groups.empty()) groups.emplace_back();
        groups.back().push_back({name, std::move(make)});
    }
    // A theory-independent encoding, run as NAME-<ELEM> or as NAME with default_element
    void add_generic(const string& name, const string& default_element, GenericFactory make) {
        generics.push_back({name, default_element, std::move(make)});
    }

    // The colorer for a theory name, or nullptr if the name is unknown.
    // Throws for a known encoding with an unknown element theory (e.g. SET-MASK-XYZ).
    unique_ptr<Colorer> create(const string& theory, int K, bool model, bool print) const {
        for (const auto& group : groups) {
            for (const auto& encoding : group) {
                if (encoding.name == theory) return encoding.make(K, model, print);
            }
        }
        for (const auto& encoding : generics) {
            string element_name;
            if (theory == encoding.name) {
                element_name = encoding.default_element;
            } else if (theory.rfind(encoding.name + "-", 0) == 0) {
                element_name = theory.substr(encoding.name.size() + 1);
            } else {
                continue;
            }
            unique_ptr<Elements> elements = make_elements(element_name);
            if (!elements) {
                throw runtime_error("Unknown element theory '" + element_name + "' in '" + theory + "'");
            }
            return encoding.make(K, model, print, std::move(elements));
        }
        return nullptr;
    }

    // The "Available Theories" and "Theory-independent encodings" parts of --help
    void print_help(ostream& out) const {
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
        if (generics.empty()) return;

        vector<string> names;
        map<string, vector<string>> by_default;  // default element -> encodings
        for (const auto& encoding : generics) {
            names.push_back(encoding.name);
            by_default[encoding.default_element].push_back(encoding.name);
        }
        out << "\nTheory-independent encodings, as <ENCODING> or <ENCODING>-<ELEM>:" << endl;
        out << "  " << join(names, ", ") << endl;
        out << "  <ELEM> is the element theory: " << join(element_names, ", ") << endl;
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

    // Everything the GUI needs, as JSON: the encodings (with their element theories and
    // whether strategies can fix colors in them) and the strategies
    void print_json(ostream& out) const {
        auto colors = [&](const string& name) {
            auto colorer = create(name, 3, false, false);
            return colorer && colorer->supports_colors();
        };
        out << "{\"encodings\":[";
        bool first = true;
        for (const auto& group : groups) {
            for (const auto& encoding : group) {
                out << (first ? "" : ",") << "{\"name\":" << json_string(encoding.name)
                    << ",\"generic\":false,\"colors\":" << (colors(encoding.name) ? "true" : "false") << "}";
                first = false;
            }
        }
        for (const auto& encoding : generics) {
            out << (first ? "" : ",") << "{\"name\":" << json_string(encoding.name) << ",\"generic\":true,\"default_element\":"
                << json_string(encoding.default_element) << ",\"colors\":" << (colors(encoding.name) ? "true" : "false") << "}";
            first = false;
        }
        out << "],\"elements\":[";
        for (size_t i = 0; i < element_names.size(); i++) out << (i ? "," : "") << json_string(element_names[i]);
        out << "],\"strategies\":[";
        const auto& list = strategies::strategy_list();
        for (size_t i = 0; i < list.size(); i++) {
            const auto& s = list[i];
            out << (i ? "," : "") << "{\"name\":" << json_string(s.name) << ",\"kind\":" << json_string(s.kind)
                << ",\"needs_colors\":" << (s.needs_colors ? "true" : "false") << ",\"description\":"
                << json_string(s.description) << ",\"parameters\":" << json_string(s.parameters) << "}";
        }
        out << "]}" << endl;
    }

private:
    struct Specific { string name; Factory make; };
    struct Generic { string name; string default_element; GenericFactory make; };
    vector<vector<Specific>> groups;
    vector<Generic> generics;
    ElementFactory make_elements;
    vector<string> element_names;

    static string join(const vector<string>& items, const string& separator) {
        string out;
        for (size_t i = 0; i < items.size(); i++) out += (i ? separator : "") + items[i];
        return out;
    }
};

// Factories for colorers whose constructor is (K, model, print, extra...) or
// (K, model, print, elements, extra...), e.g. make<BvOrderColorer>(true)
template <class Colorer, class... Extra>
auto make(Extra... extra) {
    return [=](int k, bool model, bool print) { return make_unique<Colorer>(k, model, print, extra...); };
}
template <class Colorer, class... Extra>
auto make_generic(Extra... extra) {
    return [=](int k, bool model, bool print, auto elements) {
        return make_unique<Colorer>(k, model, print, std::move(elements), extra...);
    };
}
