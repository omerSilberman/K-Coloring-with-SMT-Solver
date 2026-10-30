// The cvc5 encodings by name (see common/registry.h).
#pragma once

#include "../common/registry.h"
#include "colorer.h"
#include "elements.h"

using Cvc5Registry = Registry<Cvc5Colorer, ElementTheory>;

// One per theory file, in --help order
void register_int(Cvc5Registry& registry);        // int.cpp
void register_bv(Cvc5Registry& registry);         // bv.cpp
void register_fp(Cvc5Registry& registry);         // fp.cpp
void register_real(Cvc5Registry& registry);       // real.cpp
void register_ff(Cvc5Registry& registry);         // ff.cpp
void register_uf(Cvc5Registry& registry);         // uf.cpp
void register_datatypes(Cvc5Registry& registry);  // datatypes.cpp
void register_bool(Cvc5Registry& registry);       // bool.cpp
void register_strings(Cvc5Registry& registry);    // strings.cpp
void register_sets(Cvc5Registry& registry);       // sets.cpp
void register_arrays(Cvc5Registry& registry);     // arrays.cpp
void register_sep(Cvc5Registry& registry);        // sep.cpp
