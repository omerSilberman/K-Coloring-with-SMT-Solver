// The command line shared by every engine's binary:
//   ./<program> <THEORY> <dimacs_file> <K> [--model] [--print-asserts] [--opt NAME=VALUE]...
//               [--dump-smt2 FILE [--expected sat|unsat|unknown]]
#pragma once

#include <exception>
#include <string>

#include "colorer.h"

// program: the binary's name for usage lines; engine: the solver's name for --opt help.
// registry: the engine's Registry (see registry.h).
template <class Registry>
int run_cli(int argc, char** argv, const string& program, const string& engine, const Registry& registry) {
    bool produce_model = false;
    bool print_asserts = false;
    bool smtlib_result = false;
    vector<pair<string, string>> solver_options;
    vector<string> strategy_specs;
    vector<string> pos_args;
    string smt2_path;
    string smt2_status = "unknown";

    // The value of an option given as "--name VALUE" or "--name=VALUE" (empty if missing)
    auto option_value = [&](int& i, const string& arg, const string& name) -> string {
        if (arg == name) return i + 1 < argc ? argv[++i] : "";
        return arg.substr(name.size() + 1);
    };
    auto is_option = [](const string& arg, const string& name) {
        return arg == name || arg.rfind(name + "=", 0) == 0;
    };

    // Parse command line arguments
    for (int i = 1; i < argc; ++i) {
        string arg = argv[i];
        if (arg == "--help" || arg == "-h") {
            cout << "Usage: ./" << program << " <THEORY> <dimacs_file> <K> [OPTIONS]" << endl;
            cout << "Options:" << endl;
            cout << "  --model          Produce and print the coloring model if SAT" << endl;
            cout << "  --print-asserts  Print all asserted SMT formulas before solving" << endl;
            cout << "  --smtlib-result  Print the answer as sat/unsat/unknown (for the cluster's cmpr.py)" << endl;
            cout << "  --opt NAME=VALUE Set a " << engine << " option (repeatable), e.g. --opt "
                 << (engine == "cvc5" ? "bitblast=eager" : "smt.random_seed=7") << endl;
            cout << "                   (NAME alone means NAME=true)" << endl;
            cout << "  --strategy NAME[:PARAMS]  Run a strategy before the solver (repeatable; they run" << endl;
            cout << "                   in a fixed order whatever the order given):" << endl;
            for (const auto& s : strategies::strategy_list()) {
                cout << "                     " << s.name << " (" << s.kind << ")"
                     << (s.parameters.empty() ? "" : ", parameters: " + s.parameters) << endl;
            }
            cout << "  --dump-smt2 FILE Do not solve: write the problem to FILE as an SMT-LIB benchmark" << endl;
            cout << "  --expected sat|unsat|unknown" << endl;
            cout << "                   The answer to record in the benchmark (default: unknown)" << endl;
            cout << "  --list-json      Print the encodings and strategies as JSON, and exit" << endl;
            cout << "  --help, -h       Show this help message" << endl;
            registry.print_help(cout);
            return 0;
        } else if (arg == "--list-json") {
            registry.print_json(cout);
            return 0;
        } else if (arg == "--strategy" || arg.rfind("--strategy=", 0) == 0) {
            if (arg == "--strategy") {
                if (i + 1 >= argc) {
                    cerr << "Error: --strategy needs a name." << endl;
                    return 1;
                }
                strategy_specs.push_back(argv[++i]);
            } else {
                strategy_specs.push_back(arg.substr(11));
            }
        } else if (is_option(arg, "--dump-smt2")) {
            smt2_path = option_value(i, arg, "--dump-smt2");
            if (smt2_path.empty()) {
                cerr << "Error: --dump-smt2 needs a file name." << endl;
                return 1;
            }
        } else if (is_option(arg, "--expected")) {
            smt2_status = option_value(i, arg, "--expected");
            if (smt2_status != "sat" && smt2_status != "unsat" && smt2_status != "unknown") {
                cerr << "Error: --expected must be sat, unsat or unknown." << endl;
                return 1;
            }
        } else if (arg == "--model") {
            produce_model = true;
        } else if (arg == "--print-asserts") {
            print_asserts = true;
        } else if (arg == "--smtlib-result") {
            smtlib_result = true;
        } else if (arg == "--opt" || arg.rfind("--opt=", 0) == 0) {
            string option;
            if (arg == "--opt") {
                if (i + 1 >= argc) {
                    cerr << "Error: --opt needs NAME=VALUE." << endl;
                    return 1;
                }
                option = argv[++i];
            } else {
                option = arg.substr(6);
            }
            size_t eq = option.find('=');
            if (eq == 0 || option.empty()) {
                cerr << "Error: bad --opt '" << option << "', expected NAME=VALUE." << endl;
                return 1;
            }
            if (eq == string::npos) solver_options.push_back({option, "true"});
            else solver_options.push_back({option.substr(0, eq), option.substr(eq + 1)});
        } else {
            pos_args.push_back(arg);
        }
    }

    if (pos_args.size() < 3) {
        cerr << "Error: Missing required arguments." << endl;
        cerr << "Usage: ./" << program << " <THEORY> <dimacs_file> <K> [OPTIONS]" << endl;
        cerr << "Use --help for more information." << endl;
        return 1;
    }

    string theory = pos_args[0];
    string filename = pos_args[1];
    int K;

    try {
        K = stoi(pos_args[2]);
    } catch (...) {
        cerr << "Error: K must be an integer." << endl;
        return 1;
    }

    try {
        auto colorer = registry.create(theory, K, produce_model, print_asserts);
        if (!colorer) {
            cerr << "Error: Unknown theory '" << theory << "'." << endl;
            return 1;
        }
        colorer->set_solver_options(solver_options);
        colorer->set_strategies(strategy_specs);
        if (!smt2_path.empty()) colorer->set_smt2_dump(smt2_path, smt2_status);
        colorer->set_smtlib_result(smtlib_result);
        colorer->load_dimacs(filename);
        colorer->solve();
    } catch (const exception& e) {
        cerr << "Exception caught: " << e.what() << endl;
        return 1;
    }

    return 0;
}
