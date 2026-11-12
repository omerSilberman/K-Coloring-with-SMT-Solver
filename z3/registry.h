// The Z3 encodings by name (see common/registry.h).
#pragma once

#include "../common/registry.h"
#include "colorer.h"
#include "elements.h"

using Z3Registry = Registry<Z3Colorer, ElementTheory>;

// One per theory file, in --help order (the same files as cvc5/, minus the theories
// Z3 does not have: finite fields, bags, separation logic, trigonometry)
void register_int(Z3Registry& registry);        // int.cpp
void register_bv(Z3Registry& registry);         // bv.cpp
void register_fp(Z3Registry& registry);         // fp.cpp
void register_real(Z3Registry& registry);       // real.cpp
void register_uf(Z3Registry& registry);         // uf.cpp
void register_datatypes(Z3Registry& registry);  // datatypes.cpp
void register_bool(Z3Registry& registry);       // bool.cpp
void register_rep(Z3Registry& registry);        // rep.cpp
void register_strings(Z3Registry& registry);    // strings.cpp
void register_sets(Z3Registry& registry);       // sets.cpp
void register_arrays(Z3Registry& registry);     // arrays.cpp
