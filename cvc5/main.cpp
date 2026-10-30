// smt_solver_cvc5: graph K-coloring with cvc5, in one of many SMT encodings.
//   ./smt_solver_cvc5 <THEORY> <dimacs_file> <K> [--model] [--print-asserts] [--opt NAME=VALUE]...
#include "registry.h"

static Registry make_registry() {
    Registry registry;
    for (auto register_theory : {register_int, register_bv, register_fp, register_real, register_ff,
                                 register_uf, register_datatypes, register_bool, register_strings,
                                 register_sets, register_arrays, register_sep}) {
        registry.begin_group();
        register_theory(registry);
    }
    return registry;
}

int main(int argc, char** argv) {
    Registry registry = make_registry();
    bool produce_model = false;
    bool print_asserts = false;
    vector<pair<string, string>> cvc5_options;
    vector<string> pos_args;

    // Parse command line arguments
    for (int i = 1; i < argc; ++i) {
        string arg = argv[i];
        if (arg == "--help" || arg == "-h") {
            cout << "Usage: ./smt_solver_cvc5 <THEORY> <dimacs_file> <K> [OPTIONS]" << endl;
            cout << "Options:" << endl;
            cout << "  --model          Produce and print the coloring model if SAT" << endl;
            cout << "  --print-asserts  Print all asserted SMT formulas before solving" << endl;
            cout << "  --opt NAME=VALUE Set a cvc5 option (repeatable), e.g. --opt bitblast=eager" << endl;
            cout << "                   (NAME alone means NAME=true)" << endl;
            cout << "  --help, -h       Show this help message" << endl;
            registry.print_help(cout);
            return 0;
        } else if (arg == "--model") {
            produce_model = true;
        } else if (arg == "--print-asserts") {
            print_asserts = true;
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
            if (eq == string::npos) cvc5_options.push_back({option, "true"});
            else cvc5_options.push_back({option.substr(0, eq), option.substr(eq + 1)});
        } else {
            pos_args.push_back(arg);
        }
    }

    if (pos_args.size() < 3) {
        cerr << "Error: Missing required arguments." << endl;
        cerr << "Usage: ./smt_solver_cvc5 <THEORY> <dimacs_file> <K> [OPTIONS]" << endl;
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
        unique_ptr<AbstractGraphColorer> colorer = registry.create(theory, K, produce_model, print_asserts);
        if (!colorer) {
            cerr << "Error: Unknown theory '" << theory << "'." << endl;
            return 1;
        }
        colorer->set_cvc5_options(cvc5_options);
        colorer->load_dimacs(filename);
        colorer->solve();
    } catch (const exception& e) {
        cerr << "Exception caught: " << e.what() << endl;
        return 1;
    }

    return 0;
}
