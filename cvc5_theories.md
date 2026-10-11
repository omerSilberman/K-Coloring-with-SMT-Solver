# cvc5 theories and operators

Reference for the cvc5 version this project is built against (**cvc5 1.4.0 prerelease**). The list of operators, their argument sorts and C++ constructors come from cvc5's own sources (`include/cvc5/cvc5_kind.h` and the SMT-LIB parser), so nothing is missing or misspelled for this version.

## How to read this

Every theory section has a short introduction, the logic letters that enable it, and a table with one row per operator:

- **Kind**: the C++ name, used as `tm.mkTerm(cvc5::Kind::X, {args})`. Indexed operators (like `extract`) are built with `tm.mkTerm(tm.mkOp(cvc5::Kind::X, {indices}), {args})`.
- **SMT-LIB**: the name in `.smt2` files, which is also what `--print-asserts` prints. Empty means there is no SMT-LIB syntax (C++ only, or internal).
- **What it does**: a plain explanation, then the arguments (arity and sorts) and, for constants and values, the C++ function that creates them.
- **Example**: `term → value` means cvc5 **proved** that `term` equals `value` (or holds, for `true`): the example was run through this cvc5 binary as `(assert (not (= term value)))` and came back `unsat`. Scripts show the expected `sat`/`unsat`. Examples marked ⚠ are true but this cvc5 could not prove them, which says something about its support for that operator. Some examples need a specific logic or option, shown in small print.

A complete problem, for orientation (the triangle graph with 3 colors, as this project's `LIA` encoding builds it):

```smt2
(set-logic QF_LIA)
(declare-const n1 Int)
(declare-const n2 Int)
(declare-const n3 Int)
(assert (<= 1 n1 3))
(assert (<= 1 n2 3))
(assert (<= 1 n3 3))
(assert (distinct n1 n2 n3))
(check-sat)   ; sat
(get-model)
```

Run it with `cvc5 file.smt2` (the binary is in `smt-switch/deps/cvc5/bin/`).

## Contents

- [Choosing a logic](#choosing-a-logic)
- [Sorts](#sorts)
- [Core](#core) (9 operators)
- [Core (Boolean)](#core-boolean) (7 operators)
- [Uninterpreted functions](#uninterpreted-functions) (3 operators)
- [Arithmetic](#arithmetic) (41 operators)
- [Bit-vectors](#bit-vectors) (55 operators)
- [Finite fields](#finite-fields) (5 operators)
- [Floating-point](#floating-point) (35 operators)
- [Arrays](#arrays) (4 operators)
- [Datatypes](#datatypes) (9 operators)
- [Separation logic](#separation-logic) (5 operators)
- [Finite sets](#finite-sets) (20 operators)
- [Relations](#relations) (10 operators)
- [Bags (multisets)](#bags-multisets) (24 operators)
- [Strings, sequences and regular expressions](#strings-sequences-and-regular-expressions) (56 operators)
- [Quantifiers](#quantifiers) (10 operators)

## Choosing a logic

`solver.setLogic("...")` (or `(set-logic ...)`) decides which theories are enabled. A logic string is an optional prefix followed by theory letters, in any order, each at most once. Using a smaller logic lets cvc5 pick faster, specialized procedures; using an operator outside the logic is an error.

| Part | Meaning |
|---|---|
| `QF_` | Quantifier-free. Without it, `forall`/`exists` are allowed |
| `HO_` | Higher-order: functions are values, `lambda` and `@` can be used |
| `SEP_` | Separation logic |
| `A` / `AX` | Arrays |
| `UF` | Uninterpreted functions and sorts |
| `C` | Cardinality constraints on uninterpreted sorts |
| `BV` | Bit-vectors |
| `FF` | Finite fields |
| `FP` | Floating-point |
| `DT` | Datatypes |
| `S` | Strings and sequences |
| `FS` | Finite sets (and relations) |
| `LIA` `LRA` `LIRA` | Linear integer / real / mixed arithmetic (at most one arithmetic part) |
| `NIA` `NRA` `NIRA` | Nonlinear integer / real / mixed arithmetic; add `T` for transcendentals (`NRAT`) |
| `IDL` `RDL` `IRDL` | Difference logic (`x - y <= c`) over integers / reals / both |
| `ALL` | Everything, including bags and other theories without a letter |
| `QF_ALL` | Everything, quantifier-free |

Examples: `QF_LIA`, `QF_BV`, `QF_UFBV`, `QF_AUFLIA`, `QF_SLIA`, `QF_NRAT`, `QF_FF`, `QF_FSLIA`, `QF_DT`, `ALL`.

Logics used in this project: `QF_LIA`, `QF_IDL`, `QF_BV`, `QF_NRA`, `QF_NRAT`, `QF_FF`, `QF_UF`, `QF_DT`, `QF_S`, `QF_SLIA`, `QF_FSLIA`, `QF_ALIA`, `ALL`.

## Sorts

A sort is a type. Every term has one, and operators only accept arguments of the right sorts.

| Sort kind | SMT-LIB | Example | Description | C++ |
|---|---|---|---|---|
| `ABSTRACT_SORT` |  | Placeholder for a sort with unspecified parameters, used only in API queries. | An abstract sort. | `TermManager::mkAbstractSort(SortKind)` |
| `ARRAY_SORT` | `(Array Int Bool)` | `((as const (Array Int Bool)) false)` | An array sort, whose argument sorts are the index and element sorts of the array. | `TermManager::mkArraySort(Sort, Sort)` |
| `BAG_SORT` | `(Bag Int)` | `(bag 1 2)` | A bag sort, whose argument sort is the element sort of the bag. | `TermManager::mkBagSort(Sort)` |
| `BOOLEAN_SORT` | `Bool` | `true` | The Boolean sort. | `TermManager::getBooleanSort()` |
| `BITVECTOR_SORT` | `(_ BitVec 4)` | `#b1010` | A bit-vector sort, parameterized by an integer denoting its bit-width. | `TermManager::mkBitVectorSort(uint32_t)` |
| `DATATYPE_SORT` | declared with `declare-datatype` | `(declare-datatype Color ((Red) (Green)))` | A datatype sort. | `TermManager::mkDatatypeSort(DatatypeDecl)`<br>`TermManager::mkDatatypeSorts(const std::vector<DatatypeDecl>&)` |
| `FINITE_FIELD_SORT` | `(_ FiniteField 7)` | `#f3m7` | A finite field sort, parameterized by a size. | `TermManager::mkFiniteFieldSort(const std::string&, uint32_t base)` |
| `FLOATINGPOINT_SORT` | `(_ FloatingPoint 8 24), Float32` | `(_ +zero 8 24)` | A floating-point sort, parameterized by two integers denoting its exponent and significand bit-widths. | `TermManager::mkFloatingPointSort(uint32_t, uint32_t)` |
| `FUNCTION_SORT` | `(-> Int Int)` | `(lambda ((x Int)) x)` | A function sort with given domain sorts and codomain sort. | `TermManager::mkFunctionSort(const std::vector<Sort>&, Sort)` |
| `INTEGER_SORT` | `Int` | `42` | The integer sort. | `TermManager::getIntegerSort()` |
| `REAL_SORT` | `Real` | `3.5` | The real sort. | `TermManager::getRealSort()` |
| `REGLAN_SORT` | `RegLan` | `(re.* (str.to_re "a"))` | The regular language sort. | `TermManager::getRegExpSort()` |
| `ROUNDINGMODE_SORT` | `RoundingMode` | `RNE` | The rounding mode sort. | `TermManager::getRoundingModeSort()` |
| `SEQUENCE_SORT` | `(Seq Int)` | `(seq.unit 1)` | A sequence sort, whose argument sort is the element sort of the sequence. | `TermManager::mkSequenceSort(Sort)` |
| `SET_SORT` | `(Set Int)` | `(set.singleton 1)` | A set sort, whose argument sort is the element sort of the set. | `TermManager::mkSetSort(Sort)` |
| `STRING_SORT` | `String` | `"abc"` | The string sort. | `TermManager::getStringSort()` |
| `TUPLE_SORT` | `(Tuple Int Bool)` | `(tuple 1 true)` | A tuple sort, whose argument sorts denote the sorts of the direct children of the tuple. | `TermManager::mkTupleSort(const std::vector<Sort>&)` |
| `NULLABLE_SORT` | `(Nullable Int)` | `(nullable.some 1)` | A nullable sort, whose argument sort denotes the sort of the direct child of the nullable. | `TermManager::mkNullableSort(const Sort&)` |
| `UNINTERPRETED_SORT` | declared with `declare-sort` | `(declare-sort U 0)` | An uninterpreted sort. | `TermManager::mkUninterpretedSort(const std::optional<std::string>&)` |

## Core

The building blocks shared by every theory: equality, distinctness, and the kinds of symbols a term can be made of.

**Logic:** always available

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `UNINTERPRETED_SORT_VALUE` |  | A concrete element of an uninterpreted sort, as it appears in a model (printed like `(as @U_0 U)`). You never write these yourself; they come back from `getValue`. |  |
| `EQUAL` | `=` | True when all arguments are equal. Works for every sort, and takes 2 or more arguments (`(= a b c)` means `a = b` and `b = c`). On Booleans it means "if and only if".<br><sub>Arity `n > 1`: `1..n:` Terms of the same Sort</sub> | `(= 2 (+ 1 1) (- 3 1))` → `true` |
| `DISTINCT` | `distinct` | True when all arguments are *pairwise* different. `(distinct a b c)` is `a != b`, `a != c`, `b != c`. This project uses `(not (= u v))` per edge, and `distinct` for the color constants of the `UF` encodings.<br><sub>Arity `n > 1`: `1..n:` Terms of the same Sort</sub> | `(distinct 1 2 1)` → `false` |
| `CONSTANT` |  | A free constant: an unknown whose value the solver chooses. The node variables of every encoding in this project are constants.<br><sub>C++: `TermManager::mkConst(const Sort&, const std::optional<std::string>&)`</sub> | `(declare-const x Int)`<br>`(assert (> x 5))`<br>→ `sat` |
| `VARIABLE` |  | A *bound* variable: the `x` inside `forall`, `exists`, `lambda` or `set.comprehension`. Unlike a constant, it has no value of its own.<br><sub>C++: `TermManager::mkVar(const Sort&, const std::optional<std::string>&)`</sub> | C++: `cvc5::Term x = tm.mkVar(tm.getIntegerSort(), "x");` |
| `SKOLEM` |  | A fresh symbol the solver introduces internally (for example for the witness of an `exists`, or for division by zero). Users do not create these; they may show up in models and proofs. |  |
| `SEXPR` |  | A generic list of terms, used for options, annotations and `get-info` results. It has no logical meaning.<br><sub>Arity `n > 0`: `1..n:` Terms with same sorts</sub> | C++: `tm.mkTerm(cvc5::Kind::SEXPR, {a, b})` |
| `LAMBDA` | `lambda` | An anonymous function. `define-fun` is sugar for binding a name to a lambda; lambdas can be passed directly to higher-order operators like `set.map`, or applied in higher-order logics (`HO_ALL`).<br><sub>Arity `2`: `1:` Term of kind `VARIABLE_LIST`; `2:` Term of any Sort (the body of the lambda)</sub> | `(@ (lambda ((x Int)) (+ x 1)) 2)` → `3` <sub>(logic `HO_ALL`)</sub> |
| `WITNESS` |  | Hilbert choice: `witness x. P(x)` is *some* `x` satisfying `P`, if one exists. Used internally (for example to eliminate quantifiers); there is no standard SMT-LIB syntax.<br><sub>Arity `3`: `1:` Term of kind `VARIABLE_LIST`; `2:` Term of Sort Bool (the body of the witness); `3:` (optional) Term of kind `INST_PATTERN_LIST`</sub> | C++: `tm.mkTerm(cvc5::Kind::WITNESS, {tm.mkTerm(cvc5::Kind::VARIABLE_LIST, {x}), body})` |

## Core (Boolean)

The usual propositional connectives. Every assertion is a Boolean term, so these appear in every logic.

**Logic:** always available

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `CONST_BOOLEAN` | `true`, `false` | The constants `true` and `false`.<br><sub>C++: `TermManager::mkTrue()`<br>`TermManager::mkFalse()`<br>`TermManager::mkBoolean(bool)`</sub> | `(and true (not false))` → `true` |
| `NOT` | `not` | Negation.<br><sub>Arity `1`: `1:` Term of Sort Bool</sub> | `(not true)` → `false` |
| `AND` | `and` | True when all arguments are true (2 or more).<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Bool</sub> | `(and true true false)` → `false` |
| `IMPLIES` | `=>` | Implication; right-associative, so `(=> a b c)` is `a => (b => c)`. False only when the premise is true and the conclusion false.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Bool</sub> | `(=> false false)` → `true` |
| `OR` | `or` | True when at least one argument is true.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Bool</sub> | `(or false false true)` → `true` |
| `XOR` | `xor` | Exclusive or; with more arguments it is true when an odd number of them are true.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Bool</sub> | `(xor true true true)` → `true` |
| `ITE` | `ite` | If-then-else: `(ite c a b)` is `a` when `c` holds, else `b`. The branches can be of any (same) sort, not just Bool.<br><sub>Arity `3`: `1:` Term of Sort Bool; `2:` The 'then' term, Term of any Sort; `3:` The 'else' term, Term of the same sort as second argument</sub> | `(ite (> 3 2) 10 20)` → `10` |

## Uninterpreted functions

Uninterpreted functions and sorts. A function declared with `declare-fun` has no meaning except *congruence*: equal inputs give equal outputs. An uninterpreted sort (`declare-sort`) is a set of values about which nothing is known except which ones are equal. This project's `UF` and `LIST-UF` encodings use them.

**Logic:** `UF`

The examples in this section assume:

```smt2
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `APPLY_UF` | `(f t1 ... tn)` | Applying a function declared with `declare-fun`. The solver may choose any function, as long as equal arguments give equal results (congruence).<br><sub>Arity `n > 1`: `1:` Function Term; `2..n:` Function argument instantiation Terms of any first-class Sort</sub> | `(=> (= a b) (= (f a) (f b)))` → `true` |
| `CARDINALITY_CONSTRAINT` |  | A predicate "the uninterpreted sort `U` has at most `n` elements". Directly relevant to coloring: with a sort `Color` limited to K elements, no domain constraint per node is needed. Needs the `C` letter in the logic (e.g. `QF_UFC`) or `--finite-model-find`. No standard SMT-LIB syntax.<br><sub>C++: `TermManager::mkCardinalityConstraint(const Sort&, uint32_t)`</sub> | C++: `solver.assertFormula(tm.mkCardinalityConstraint(color_sort, K));` |
| `HO_APPLY` | `@` | Higher-order application: `(@ f x)` applies a function *value* to one argument, so partial application is possible. Only in higher-order logics (`HO_ALL`).<br><sub>Arity `n = 2`: `1:` Function Term; `2:` Argument Term of the domain Sort of the function</sub> | `(= (@ f a) (f a))` → `true` <sub>(logic `HO_ALL`)</sub> |

## Arithmetic

Integers (`Int`) and reals (`Real`). Linear arithmetic (only multiplication by constants) is decidable and fast (simplex); nonlinear arithmetic (`x*y`, `x^2`) is much harder, and transcendental functions (`sin`, `exp`) are handled by incremental linearization, which can prove UNSAT but often answers `unknown` instead of SAT. In SMT-LIB, `5` is an `Int` and `5.0` a `Real`, and negative numbers are written `(- 5)`. This project's `LIA`, `IDL`, `NLRA` and `NLRA-*` encodings use this theory.

**Logic:** `LIA`, `LRA`, `LIRA`, `NIA`, `NRA`, `NIRA`, `IDL`, `RDL`, `IRDL`; append `T` (e.g. `NRAT`) for transcendentals

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `ADD` | `+` | Sum of 2 or more numbers.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Int or Real (sorts must match)</sub> | `(+ 1 2 3)` → `6` |
| `MULT` | `*` | Product of 2 or more numbers. Multiplying two non-constant terms makes the problem nonlinear.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Int or Real (sorts must match)</sub> | `(* 2 3 4)` → `24` |
| `IAND` | `iand` | Bitwise AND on integers, indexed by a width `k`: both arguments are taken modulo 2^k, ANDed bit by bit, and the result is an integer. Bridges integer and bit-vector reasoning without changing sort. 12 = `1100`, 10 = `1010`. | `((_ iand 4) 12 10)` → `8` |
| `PIAND` | `piand` | Like `iand`, but the width is an ordinary argument, so it can be symbolic: `(piand k x y)`. Gives 0 when `k <= 0`. | `(piand 4 12 10)` → `8` |
| `POW2` | `int.pow2` | `2^x` for an integer `x >= 0`.<br><sub>Arity `1`: `1:` Term of Sort Int</sub> | `(int.pow2 10)` → `1024` |
| `LOG2` | `int.log2` | Base-2 logarithm of an integer, rounded down (the inverse of `int.pow2`).<br><sub>Arity `1`: `1:` Term of Sort Int</sub> | `(int.log2 9)` → `3` |
| `SUB` | `-` | Subtraction, left-associative: `(- a b c)` is `(a - b) - c`.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Int or Real (sorts must match)</sub> | `(- 10 3 2)` → `5` |
| `NEG` | `-` | Unary minus. Also how negative literals are written in SMT-LIB.<br><sub>Arity `1`: `1:` Term of Sort Int or Real</sub> | `(- 5)` → `(- 0 5)` |
| `DIVISION` | `/` | Real division. Division by 0 is not an error: `(/ x 0.0)` is some unknown value chosen by the solver (but the same value for the same `x`).<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Real</sub> | `(/ 7.0 2.0)` → `3.5` |
| `DIVISION_TOTAL` | `/_total` | Real division where dividing by 0 gives 0. cvc5-specific.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Real</sub> | `(/_total 7.0 0.0)` → `0.0` |
| `INTS_DIVISION` | `div` | Integer division, rounding so that the remainder `mod` is always `>= 0` (SMT-LIB's Euclidean division). So `-7 div 2` is `-4`, not `-3`. Division by 0 is an unknown value.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Int</sub> | `(div (- 7) 2)` → `(- 4)` |
| `INTS_DIVISION_TOTAL` | `div_total` | Integer division where dividing by 0 gives 0. cvc5-specific.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Int</sub> | `(div_total 7 0)` → `0` |
| `INTS_MODULUS` | `mod` | Remainder matching `div`: always between 0 and `\|divisor\| - 1`, and `x = y*(div x y) + (mod x y)`.<br><sub>Arity `2`: `1:` Term of Sort Int; `2:` Term of Sort Int</sub> | `(mod (- 7) 3)` → `2` |
| `INTS_MODULUS_TOTAL` | `mod_total` | Integer remainder where `x mod 0` is `x`. cvc5-specific.<br><sub>Arity `2`: `1:` Term of Sort Int; `2:` Term of Sort Int</sub> | `(mod_total 7 0)` → `7` |
| `ABS` | `abs` | Absolute value.<br><sub>Arity `1`: `1:` Term of Sort Int or Real</sub> | `(abs (- 4))` → `4` |
| `POW` | `^` | Power `x^n`. cvc5 handles it when the exponent is a constant natural number (it becomes repeated multiplication).<br><sub>Arity `2`: `1..2:` Term of Sort Int or Real (sorts must match)</sub> | `(^ 2 10)` → `1024` |
| `EXPONENTIAL` | `exp` | e^x (transcendental; needs a logic with `T`, like `QF_NRAT`).<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(exp 0.0)` → `1.0` |
| `SINE` | `sin` | Sine (radians). This project's `NLRA-SIN` encoding uses its roots `n*pi` as colors.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(sin 0.0)` → `0.0` |
| `COSINE` | `cos` | Cosine (radians).<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(cos 0.0)` → `1.0` |
| `TANGENT` | `tan` | Tangent, `sin x / cos x`.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(tan 0.0)` → `0.0` |
| `COSECANT` | `csc` | Cosecant, `1 / sin x`.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(= (csc real.pi) (/ 1.0 (sin real.pi)))` → `true` |
| `SECANT` | `sec` | Secant, `1 / cos x`.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(sec 0.0)` → `1.0` |
| `COTANGENT` | `cot` | Cotangent, `cos x / sin x`.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(= (cot real.pi) (/ (cos real.pi) (sin real.pi)))` → `true` |
| `ARCSINE` | `arcsin` | Inverse sine, with values in `[-pi/2, pi/2]`.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(arcsin 0.0)` → `0.0` |
| `ARCCOSINE` | `arccos` | Inverse cosine, with values in `[0, pi]`.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(arccos 1.0)` → `0.0` ⚠ *cvc5 could not prove this (timed out)* |
| `ARCTANGENT` | `arctan` | Inverse tangent, with values in `(-pi/2, pi/2)`.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(arctan 0.0)` → `0.0` ⚠ *cvc5 could not prove this (answered unknown)* |
| `ARCCOSECANT` | `arccsc` | Inverse cosecant.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(arccsc 1.0)` → `(/ real.pi 2.0)` ⚠ *cvc5 could not prove this (answered sat)* |
| `ARCSECANT` | `arcsec` | Inverse secant.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(arcsec 1.0)` → `0.0` ⚠ *cvc5 could not prove this (answered sat)* |
| `ARCCOTANGENT` | `arccot` | Inverse cotangent.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(arccot 0.0)` → `(/ real.pi 2.0)` ⚠ *cvc5 could not prove this (answered sat)* |
| `SQRT` | `sqrt` | Square root of a non-negative real.<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(sqrt 4.0)` → `2.0` |
| `DIVISIBLE` | `divisible` | Divisibility test, indexed by the divisor: `((_ divisible n) x)` holds when `n` divides `x`. | `((_ divisible 3) 9)` → `true` |
| `CONST_RATIONAL` | `1.5`, `(/ 1 2)` | An exact rational number (arbitrary precision, never rounded). Written as a decimal or as a division of literals.<br><sub>C++: `TermManager::mkReal(const std::string&)`<br>`TermManager::mkReal(int64_t)`<br>`TermManager::mkReal(int64_t, int64_t)`</sub> | `(+ 1.5 (/ 1 2))` → `2.0` |
| `CONST_INTEGER` | `5` | An arbitrary-precision integer literal (no overflow).<br><sub>C++: `TermManager::mkInteger(const std::string&)`<br>`TermManager::mkInteger(int64_t)`</sub> | `(* 100000000000 100000000000)` → `10000000000000000000000` |
| `LT` | `<` | Less than; chainable, so `(< a b c)` means `a < b < c`.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Int or Real (sorts must match)</sub> | `(< 1 2 3)` → `true` |
| `LEQ` | `<=` | Less than or equal; chainable. This project's `LIA` domain is `(<= 1 x K)` in this form.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Int or Real (sorts must match)</sub> | `(<= 1 1 2)` → `true` |
| `GT` | `>` | Greater than; chainable.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Int or Real (sorts must match)</sub> | `(> 3 2 2)` → `false` |
| `GEQ` | `>=` | Greater than or equal; chainable.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort Int or Real (sorts must match)</sub> | `(>= 3 2 2)` → `true` |
| `IS_INTEGER` | `is_int` | Whether a real has no fractional part.<br><sub>Arity `1`: `1:` Term of Sort Int or Real</sub> | `(is_int 2.5)` → `false` |
| `TO_INTEGER` | `to_int` | Floor: the largest integer `<=` the argument (so it rounds negatives *down*).<br><sub>Arity `1`: `1:` Term of Sort Int or Real</sub> | `(to_int (- 2.5))` → `(- 3)` |
| `TO_REAL` | `to_real` | Converts an integer to a real, for mixing `Int` and `Real` (`LIRA`).<br><sub>Arity `1`: `1:` Term of Sort Int or Real</sub> | `(to_real 3)` → `3.0` |
| `PI` | `real.pi` | The constant pi. cvc5 reasons about it through rational lower and upper bounds.<br><sub>C++: `TermManager::mkPi()`</sub> | `(< 3.14 real.pi 3.15)` → `true` |

## Bit-vectors

Fixed-width bit-vectors, i.e. machine integers. `(_ BitVec 4)` has the 16 values `#b0000` to `#b1111`. Arithmetic wraps around modulo 2^w. A bit-vector has no sign of its own: operators come in unsigned (`bvult`, `bvudiv`) and signed two's complement (`bvslt`, `bvsdiv`) versions. Bit `0` is the rightmost bit. cvc5 solves bit-vectors mostly by *bit-blasting* them into a SAT problem. This project's `BV`, `BV-ZERO`, `BV-AND` and `BV-ONEHOT` encodings use this theory. The examples use width 4.

**Logic:** `BV`

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `CONST_BITVECTOR` | `#b0101`, `#x1f`, `(_ bv5 4)` | A bit-vector literal. `#b...` gives one bit per digit, `#x...` four bits per hex digit, and `(_ bvN w)` the number N at width w.<br><sub>C++: `TermManager::mkBitVector(uint32_t, uint64_t)`<br>`TermManager::mkBitVector(uint32_t, const std::string&, uint32_t)`</sub> | `(= #b0101 #x5 (_ bv5 4))` → `true` |
| `BITVECTOR_CONCAT` | `concat` | Glues bit-vectors together; the first argument becomes the high (left) bits.<br><sub>Arity `n > 1`: `1..n:` Terms of bit-vector Sort (sorts must match)</sub> | `(concat #b11 #b00)` → `#b1100` |
| `BITVECTOR_AND` | `bvand` | Bitwise AND. `BV-AND` builds its domain constraints from this.<br><sub>Arity `n > 1`: `1..n:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvand #b1100 #b1010)` → `#b1000` |
| `BITVECTOR_OR` | `bvor` | Bitwise OR.<br><sub>Arity `n > 1`: `1..n:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvor #b1100 #b1010)` → `#b1110` |
| `BITVECTOR_XOR` | `bvxor` | Bitwise exclusive or.<br><sub>Arity `n > 1`: `1..n:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvxor #b1100 #b1010)` → `#b0110` |
| `BITVECTOR_NOT` | `bvnot` | Flips every bit.<br><sub>Arity `1`: `1:` Term of bit-vector Sort</sub> | `(bvnot #b1100)` → `#b0011` |
| `BITVECTOR_NAND` | `bvnand` | Bitwise NOT-AND.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvnand #b1100 #b1010)` → `#b0111` |
| `BITVECTOR_NOR` | `bvnor` | Bitwise NOT-OR.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvnor #b1100 #b1010)` → `#b0001` |
| `BITVECTOR_XNOR` | `bvxnor` | Bitwise NOT-XOR (1 where the bits are equal).<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvxnor #b1100 #b1010)` → `#b1001` |
| `BITVECTOR_COMP` | `bvcomp` | Equality as a 1-bit vector: `#b1` if equal, else `#b0`.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvcomp #b1010 #b1010)` → `#b1` |
| `BITVECTOR_MULT` | `bvmul` | Multiplication modulo 2^w (overflow wraps). 6 * 3 = 18 = 16 + 2.<br><sub>Arity `n > 1`: `1..n:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvmul #b0110 #b0011)` → `#b0010` |
| `BITVECTOR_ADD` | `bvadd` | Addition modulo 2^w.<br><sub>Arity `n > 1`: `1..n:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvadd #b1111 #b0001)` → `#b0000` |
| `BITVECTOR_SUB` | `bvsub` | Subtraction modulo 2^w. `BV-ONEHOT` uses `x - 1`.<br><sub>Arity `n > 1`: `1..n:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsub #b0000 #b0001)` → `#b1111` |
| `BITVECTOR_NEG` | `bvneg` | Two's complement negation (`0 - x`).<br><sub>Arity `1`: `1:` Term of bit-vector Sort</sub> | `(bvneg #b0001)` → `#b1111` |
| `BITVECTOR_UDIV` | `bvudiv` | Unsigned division, rounding down. Dividing by 0 gives all ones.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvudiv #b0111 #b0000)` → `#b1111` |
| `BITVECTOR_UREM` | `bvurem` | Unsigned remainder. Remainder by 0 gives the dividend.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvurem #b0111 #b0010)` → `#b0001` |
| `BITVECTOR_SDIV` | `bvsdiv` | Signed division, rounding toward zero. Here -7 / 2 = -3.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsdiv #b1001 #b0010)` → `#b1101` |
| `BITVECTOR_SREM` | `bvsrem` | Signed remainder whose sign follows the dividend (like C's `%`). -7 rem 2 = -1.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsrem #b1001 #b0010)` → `#b1111` |
| `BITVECTOR_SMOD` | `bvsmod` | Signed remainder whose sign follows the divisor (like Python's `%`). -7 mod 2 = 1.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsmod #b1001 #b0010)` → `#b0001` |
| `BITVECTOR_SHL` | `bvshl` | Shift left by the amount in the second argument, filling with 0.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvshl #b0011 #b0010)` → `#b1100` |
| `BITVECTOR_LSHR` | `bvlshr` | Logical shift right, filling with 0.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvlshr #b1100 #b0010)` → `#b0011` |
| `BITVECTOR_ASHR` | `bvashr` | Arithmetic shift right, filling with copies of the sign bit.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvashr #b1000 #b0010)` → `#b1110` |
| `BITVECTOR_ULT` | `bvult` | Unsigned `<`.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvult #b0001 #b1000)` → `true` |
| `BITVECTOR_ULE` | `bvule` | Unsigned `<=`. This project's `BV` and `BV-ZERO` domain bounds.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvule #b1000 #b1000)` → `true` |
| `BITVECTOR_UGT` | `bvugt` | Unsigned `>`.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvugt #b1000 #b0001)` → `true` |
| `BITVECTOR_UGE` | `bvuge` | Unsigned `>=`.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvuge #b0001 #b1000)` → `false` |
| `BITVECTOR_SLT` | `bvslt` | Signed `<`. `#b1000` is -8, the smallest 4-bit value.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvslt #b1000 #b0001)` → `true` |
| `BITVECTOR_SLE` | `bvsle` | Signed `<=`.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsle #b1111 #b0000)` → `true` |
| `BITVECTOR_SGT` | `bvsgt` | Signed `>`.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsgt #b0111 #b1000)` → `true` |
| `BITVECTOR_SGE` | `bvsge` | Signed `>=`.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsge #b1111 #b0000)` → `false` |
| `BITVECTOR_ULTBV` |  | Unsigned `<` that returns a 1-bit vector (`#b1`/`#b0`) instead of a Bool. Internal; no SMT-LIB syntax.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | C++: `tm.mkTerm(cvc5::Kind::BITVECTOR_ULTBV, {x, y})` |
| `BITVECTOR_SLTBV` |  | Signed `<` that returns a 1-bit vector. Internal; no SMT-LIB syntax.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | C++: `tm.mkTerm(cvc5::Kind::BITVECTOR_SLTBV, {x, y})` |
| `BITVECTOR_ITE` | `bvite` | If-then-else whose condition is a 1-bit vector.<br><sub>Arity `3`: `1:` Term of bit-vector Sort of size `1`; `1..3:` Terms of bit-vector sort (sorts must match)</sub> | `(bvite #b1 #b1010 #b0101)` → `#b1010` |
| `BITVECTOR_REDOR` | `bvredor` | OR of all bits: `#b1` when any bit is set.<br><sub>Arity `1`: `1:` Term of bit-vector Sort</sub> | `(bvredor #b0100)` → `#b1` |
| `BITVECTOR_REDAND` | `bvredand` | AND of all bits: `#b1` only when every bit is set.<br><sub>Arity `1`: `1:` Term of bit-vector Sort</sub> | `(bvredand #b1101)` → `#b0` |
| `BITVECTOR_NEGO` | `bvnego` | True when signed negation overflows (only for the minimum value: -(-8) does not fit in 4 bits).<br><sub>Arity `1`: `1:` Term of bit-vector Sort</sub> | `(bvnego #b1000)` → `true` |
| `BITVECTOR_UADDO` | `bvuaddo` | True when unsigned addition overflows.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvuaddo #b1111 #b0001)` → `true` |
| `BITVECTOR_SADDO` | `bvsaddo` | True when signed addition overflows (7 + 1 > 7).<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsaddo #b0111 #b0001)` → `true` |
| `BITVECTOR_UMULO` | `bvumulo` | True when unsigned multiplication overflows.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvumulo #b1000 #b0010)` → `true` |
| `BITVECTOR_SMULO` | `bvsmulo` | True when signed multiplication overflows (4 * 2 > 7).<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsmulo #b0100 #b0010)` → `true` |
| `BITVECTOR_USUBO` | `bvusubo` | True when unsigned subtraction underflows.<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvusubo #b0000 #b0001)` → `true` |
| `BITVECTOR_SSUBO` | `bvssubo` | True when signed subtraction overflows (-8 - 1 < -8).<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvssubo #b1000 #b0001)` → `true` |
| `BITVECTOR_SDIVO` | `bvsdivo` | True when signed division overflows (only -8 / -1 = 8).<br><sub>Arity `2`: `1..2:` Terms of bit-vector Sort (sorts must match)</sub> | `(bvsdivo #b1000 #b1111)` → `true` |
| `BITVECTOR_EXTRACT` | `extract` | Takes bits `i` down to `j` (inclusive), indexed: `((_ extract i j) x)`.<br><sub>Arity `1`: `1:` Term of bit-vector Sort<br>Indices `2`: `1:` The upper bit index.; `2:` The lower bit index.</sub> | `((_ extract 2 1) #b0110)` → `#b11` |
| `BITVECTOR_REPEAT` | `repeat` | Concatenates `n` copies.<br><sub>Arity `1`: `1:` Term of bit-vector Sort<br>Indices `1`: `1:` The number of times to repeat the given term.</sub> | `((_ repeat 3) #b10)` → `#b101010` |
| `BITVECTOR_ZERO_EXTEND` | `zero_extend` | Adds `n` zero bits on the left (keeps the unsigned value).<br><sub>Arity `1`: `1:` Term of bit-vector Sort<br>Indices `1`: `1:` The number of zeroes to extend the given term with.</sub> | `((_ zero_extend 2) #b11)` → `#b0011` |
| `BITVECTOR_SIGN_EXTEND` | `sign_extend` | Adds `n` copies of the sign bit on the left (keeps the signed value).<br><sub>Arity `1`: `1:` Term of bit-vector Sort<br>Indices `1`: `1:` The number of bits (of the value of the sign bit) to extend the given term with.</sub> | `((_ sign_extend 2) #b10)` → `#b1110` |
| `BITVECTOR_ROTATE_LEFT` | `rotate_left` | Rotates left by `n`: bits shifted out on the left come back on the right.<br><sub>Arity `1`: `1:` Term of bit-vector Sort<br>Indices `1`: `1:` The number of bits to rotate the given term left.</sub> | `((_ rotate_left 1) #b1001)` → `#b0011` |
| `BITVECTOR_ROTATE_RIGHT` | `rotate_right` | Rotates right by `n`.<br><sub>Arity `1`: `1:` Term of bit-vector Sort<br>Indices `1`: `1:` The number of bits to rotate the given term right.</sub> | `((_ rotate_right 1) #b1001)` → `#b1100` |
| `INT_TO_BITVECTOR` | `int2bv`, `int_to_bv` | Integer to bit-vector of width `w`, modulo 2^w. 18 mod 16 = 2.<br><sub>Arity `1`: `1:` Term of Sort Int<br>Indices `1`: `1:` The size of the bit-vector to convert to.</sub> | `((_ int_to_bv 4) 18)` → `#b0010` |
| `BITVECTOR_TO_NAT` |  | Old name for unsigned bit-vector to integer; use `BITVECTOR_UBV_TO_INT`.<br><sub>Arity `1`: `1:` Term of bit-vector Sort</sub> | C++: `tm.mkTerm(cvc5::Kind::BITVECTOR_TO_NAT, {x})` |
| `BITVECTOR_UBV_TO_INT` | `bv2nat`, `ubv_to_int` | Reads a bit-vector as an unsigned integer.<br><sub>Arity `1`: `1:` Term of bit-vector Sort</sub> | `(ubv_to_int #b1111)` → `15` |
| `BITVECTOR_SBV_TO_INT` | `sbv_to_int` | Reads a bit-vector as a signed (two's complement) integer.<br><sub>Arity `1`: `1:` Term of bit-vector Sort</sub> | `(sbv_to_int #b1111)` → `(- 1)` |
| `BITVECTOR_FROM_BOOLS` |  | A bit-vector built from a list of Bool terms. Appears only in values cvc5 returns (for example from the bit-blaster); it cannot be created or asserted.<br><sub>Arity `n > 0`: `1..n:` Terms of Sort Bool</sub> |  |
| `BITVECTOR_BIT` |  | Bit `i` of a bit-vector as a Bool. Appears only in values cvc5 returns; it cannot be created or asserted. To test a bit yourself, use `(= ((_ extract i i) x) #b1)`.<br><sub>Arity `1`: `1:` Term of bit-vector Sort<br>Indices `1`: `1:` The bit index</sub> |  |

## Finite fields

Arithmetic in the prime field GF(p): the integers `0 .. p-1` with `+` and `*` modulo p. The sort is `(_ FiniteField p)`. cvc5 solves these with Gröbner-basis methods (from the CoCoA library) rather than bit-blasting. This project's `FF-*` encodings use this theory. The examples use p = 7.

**Logic:** `FF`

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `CONST_FINITE_FIELD` | `#f3m7`, `(as ff3 (_ FiniteField 7))` | A field element. `#f3m7` is 3 in GF(7); the long form is `(as ff3 (_ FiniteField 7))`. In C++ the value is a string, so it can exceed 64 bits.<br><sub>C++: `TermManager::mkFiniteFieldElem(const std::string&, const Sort&, uint32_t base)`</sub> | `(= #f3m7 (as ff3 (_ FiniteField 7)))` → `true` |
| `FINITE_FIELD_NEG` | `ff.neg` | Additive inverse: `p - x`.<br><sub>Arity `1`: `1:` Term of finite field Sort</sub> | `(ff.neg #f2m7)` → `#f5m7` |
| `FINITE_FIELD_ADD` | `ff.add` | Addition modulo p. 5 + 4 = 9 = 2 (mod 7).<br><sub>Arity `n > 1`: `1..n:` Terms of finite field Sort (sorts must match)</sub> | `(ff.add #f5m7 #f4m7)` → `#f2m7` |
| `FINITE_FIELD_BITSUM` | `ff.bitsum` | `x0 + 2*x1 + 4*x2 + ...`: reassembles a number from bits. Useful for range checks with bit decomposition. Here 1 + 0 + 4 = 5.<br><sub>Arity `n > 1`: `1..n:` Terms of finite field Sort (sorts must match)</sub> | `(ff.bitsum #f1m7 #f0m7 #f1m7)` → `#f5m7` |
| `FINITE_FIELD_MULT` | `ff.mul` | Multiplication modulo p. 3 * 5 = 15 = 1 (mod 7), so 5 is the inverse of 3. `FF-POLY` and `FF-ROOTS` use it to build their polynomials.<br><sub>Arity `n > 1`: `1..n:` Terms of finite field Sort (sorts must match)</sub> | `(ff.mul #f3m7 #f5m7)` → `#f1m7` |

## Floating-point

IEEE 754 floating-point numbers. `(_ FloatingPoint eb sb)` has `eb` exponent bits and `sb` significand bits (including the hidden bit); `Float32`, `Float32`, `Float64` and `Float128` are shorthands. Every operation that can round takes a rounding mode first. There are signed zeros, infinities and NaN, and `fp.eq` (IEEE equality) differs from `=` (identical values). cvc5 solves FP by translating to bit-vectors. The examples use `Float32` (8 exponent bits, 24 significand bits) and the constants below. Note: this cvc5 build only accepts `Float32` and `Float64` by default; other sizes need `--fp-exp` (experimental).

**Logic:** `FP`

The examples in this section assume:

```smt2
(define-fun h () Float32 ((_ to_fp 8 24) RNE 0.5))
(define-fun one () Float32 ((_ to_fp 8 24) RNE 1.0))
(define-fun two () Float32 ((_ to_fp 8 24) RNE 2.0))
(define-fun two.5 () Float32 ((_ to_fp 8 24) RNE 2.5))
(define-fun three () Float32 ((_ to_fp 8 24) RNE 3.0))
(define-fun four () Float32 ((_ to_fp 8 24) RNE 4.0))
(define-fun five () Float32 ((_ to_fp 8 24) RNE 5.0))
(define-fun m1 () Float32 ((_ to_fp 8 24) RNE (- 1.0)))
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `CONST_FLOATINGPOINT` |  | A floating-point literal. Besides `fp` triples, there are special values `(_ +zero eb sb)`, `(_ -zero eb sb)`, `(_ +oo eb sb)`, `(_ -oo eb sb)` and `(_ NaN eb sb)`.<br><sub>C++: `TermManager::mkFloatingPoint(uint32_t, uint32_t, Term)`</sub> | `(fp.isInfinite (_ +oo 8 24))` → `true` |
| `CONST_ROUNDINGMODE` | `RNE`, `RNA`, `RTP`, `RTN`, `RTZ` | Rounding modes: `RNE` (nearest, ties to even; the usual default), `RNA` (nearest, ties away from zero), `RTP` (toward +infinity), `RTN` (toward -infinity), `RTZ` (toward zero). 1/3 is not representable, so rounding down and up give different results.<br><sub>C++: `TermManager::mkRoundingMode(RoundingMode)`</sub> | `(fp.lt ((_ to_fp 8 24) RTZ (/ 1.0 3.0)) ((_ to_fp 8 24) RTP (/ 1.0 3.0)))` → `true` |
| `FLOATINGPOINT_FP` | `fp` | Builds a float from its IEEE fields: sign bit, exponent bits, significand bits (without the hidden bit). 1.0 in `Float32` has exponent `01111111` (the bias, 127) and significand 0.<br><sub>Arity `3`: `1:` Term of bit-vector Sort of size `1` (sign bit); `2:` Term of bit-vector Sort of exponent size (exponent); `3:` Term of bit-vector Sort of significand size - 1 (significand without hidden bit)</sub> | `(fp #b0 #b01111111 #b00000000000000000000000)` → `one` |
| `FLOATINGPOINT_EQ` | `fp.eq` | IEEE equality: `+0` equals `-0`, and NaN equals nothing (not even itself). Plain `=` is the opposite on both counts.<br><sub>Arity `2`: `1..2:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.eq (_ +zero 8 24) (_ -zero 8 24))` → `true` |
| `FLOATINGPOINT_ABS` | `fp.abs` | Absolute value (clears the sign bit).<br><sub>Arity `1`: `1:` Term of floating-point Sort</sub> | `(fp.abs m1)` → `one` |
| `FLOATINGPOINT_NEG` | `fp.neg` | Negation (flips the sign bit).<br><sub>Arity `1`: `1:` Term of floating-point Sort</sub> | `(fp.neg one)` → `m1` |
| `FLOATINGPOINT_ADD` | `fp.add` | Addition, rounded with the given mode.<br><sub>Arity `3`: `1:` Term of Sort RoundingMode; `2..3:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.add RNE one two)` → `three` |
| `FLOATINGPOINT_SUB` | `fp.sub` | Subtraction, rounded.<br><sub>Arity `3`: `1:` Term of Sort RoundingMode; `2..3:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.sub RNE three one)` → `two` |
| `FLOATINGPOINT_MULT` | `fp.mul` | Multiplication, rounded.<br><sub>Arity `3`: `1:` Term of Sort RoundingMode; `2..3:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.mul RNE two two)` → `four` |
| `FLOATINGPOINT_DIV` | `fp.div` | Division, rounded. Dividing by zero gives an infinity (or NaN for 0/0).<br><sub>Arity `3`: `1:` Term of Sort RoundingMode; `2..3:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.div RNE one two)` → `h` |
| `FLOATINGPOINT_FMA` | `fp.fma` | Fused multiply-add `x*y + z` with a single rounding at the end.<br><sub>Arity `4`: `1:` Term of Sort RoundingMode; `2..4:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.fma RNE two two one)` → `five` |
| `FLOATINGPOINT_SQRT` | `fp.sqrt` | Square root, rounded.<br><sub>Arity `2`: `1:` Term of Sort RoundingMode; `2:` Term of floating-point Sort</sub> | `(fp.sqrt RNE four)` → `two` |
| `FLOATINGPOINT_REM` | `fp.rem` | IEEE remainder `x - y*n`, where `n` is `x/y` rounded to the *nearest* integer (so it can be negative). 3 rem 2 = 3 - 2*2 = -1.<br><sub>Arity `2`: `1..2:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.rem three two)` → `m1` |
| `FLOATINGPOINT_RTI` | `fp.roundToIntegral` | Rounds to an integral value using the rounding mode. With `RNE`, 2.5 goes to 2 (ties to even).<br><sub>Arity `2`: `1..2:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.roundToIntegral RNE two.5)` → `two` |
| `FLOATINGPOINT_MIN` | `fp.min` | Minimum.<br><sub>Arity `2`: `1:` Term of Sort RoundingMode; `2:` Term of floating-point Sort</sub> | `(fp.min one two)` → `one` |
| `FLOATINGPOINT_MAX` | `fp.max` | Maximum.<br><sub>Arity `2`: `1..2:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.max one two)` → `two` |
| `FLOATINGPOINT_LEQ` | `fp.leq` | IEEE `<=` (false whenever a NaN is involved).<br><sub>Arity `2`: `1..2:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.leq one one)` → `true` |
| `FLOATINGPOINT_LT` | `fp.lt` | IEEE `<`.<br><sub>Arity `2`: `1..2:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.lt one two)` → `true` |
| `FLOATINGPOINT_GEQ` | `fp.geq` | IEEE `>=`.<br><sub>Arity `2`: `1..2:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.geq one two)` → `false` |
| `FLOATINGPOINT_GT` | `fp.gt` | IEEE `>`.<br><sub>Arity `2`: `1..2:` Terms of floating-point Sort (sorts must match)</sub> | `(fp.gt two one)` → `true` |
| `FLOATINGPOINT_IS_NORMAL` | `fp.isNormal` | True for normal numbers (not zero, subnormal, infinite or NaN).<br><sub>Arity `1`: `1:` Term of floating-point Sort</sub> | `(fp.isNormal one)` → `true` |
| `FLOATINGPOINT_IS_SUBNORMAL` | `fp.isSubnormal` | True for subnormal numbers (exponent field all zeros, nonzero significand): the tiny values between 0 and the smallest normal number.<br><sub>Arity `1`: `1:` Term of floating-point Sort</sub> | `(fp.isSubnormal (fp #b0 #b00000000 #b00000000000000000000001))` → `true` |
| `FLOATINGPOINT_IS_ZERO` | `fp.isZero` | True for `+0` and `-0`.<br><sub>Arity `1`: `1:` Term of floating-point Sort</sub> | `(fp.isZero (_ -zero 8 24))` → `true` |
| `FLOATINGPOINT_IS_INF` | `fp.isInfinite` | True for `+oo` and `-oo`.<br><sub>Arity `1`: `1:` Term of floating-point Sort</sub> | `(fp.isInfinite (fp.div RNE one (_ +zero 8 24)))` → `true` |
| `FLOATINGPOINT_IS_NAN` | `fp.isNaN` | True for NaN.<br><sub>Arity `1`: `1:` Term of floating-point Sort</sub> | `(fp.isNaN (fp.div RNE (_ +zero 8 24) (_ +zero 8 24)))` → `true` |
| `FLOATINGPOINT_IS_NEG` | `fp.isNegative` | True for negative values, including `-0` but not NaN.<br><sub>Arity `1`: `1:` Term of floating-point Sort</sub> | `(fp.isNegative m1)` → `true` |
| `FLOATINGPOINT_IS_POS` | `fp.isPositive` | True for positive values, including `+0` but not NaN.<br><sub>Arity `1`: `1:` Term of floating-point Sort</sub> | `(fp.isPositive one)` → `true` |
| `FLOATINGPOINT_TO_FP_FROM_IEEE_BV` | `to_fp_bv` | Reinterprets a bit-vector as the IEEE bit pattern of a float (no rounding). 1.0 in `Float32` is `0x3F800000`. Written `(_ to_fp eb sb)` applied to one bit-vector.<br><sub>Arity `1`: `1:` Term of bit-vector Sort<br>Indices `2`: `1:` The exponent size; `2:` The significand size</sub> | `((_ to_fp 8 24) #x3f800000)` → `one` |
| `FLOATINGPOINT_TO_FP_FROM_FP` | `to_fp_fp` | Converts between float formats, rounding if needed. Written `(_ to_fp eb sb)` with a rounding mode and a float.<br><sub>Arity `2`: `1:` Term of Sort RoundingMode; `2:` Term of floating-point Sort<br>Indices `2`: `1:` The exponent size; `2:` The significand size</sub> | `((_ to_fp 8 24) RNE ((_ to_fp 11 53) RNE 1.0))` → `one` |
| `FLOATINGPOINT_TO_FP_FROM_REAL` | `to_fp_real` | Rounds a real to the nearest float in the given mode. Written `(_ to_fp eb sb)` with a rounding mode and a real.<br><sub>Arity `2`: `1:` Term of Sort RoundingMode; `2:` Term of Sort Real<br>Indices `2`: `1:` The exponent size; `2:` The significand size</sub> | `((_ to_fp 8 24) RNE 3.0)` → `three` |
| `FLOATINGPOINT_TO_FP_FROM_SBV` | `to_fp_signed` | Converts a signed bit-vector integer to a float. Written `(_ to_fp eb sb)` with a rounding mode and a bit-vector.<br><sub>Arity `2`: `1:` Term of Sort RoundingMode; `2:` Term of bit-vector Sort<br>Indices `2`: `1:` The exponent size; `2:` The significand size</sub> | `((_ to_fp 8 24) RNE #b1111)` → `m1` |
| `FLOATINGPOINT_TO_FP_FROM_UBV` | `to_fp_unsigned` | Converts an unsigned bit-vector integer to a float.<br><sub>Arity `2`: `1:` Term of Sort RoundingMode; `2:` Term of bit-vector Sort<br>Indices `2`: `1:` The exponent size; `2:` The significand size</sub> | `((_ to_fp_unsigned 8 24) RNE #b0101)` → `five` |
| `FLOATINGPOINT_TO_UBV` | `fp.to_ubv` | Float to unsigned bit-vector of width `w`, rounding with the mode. Out of range or NaN gives an unspecified value.<br><sub>Arity `2`: `1:` Term of Sort RoundingMode; `2:` Term of floating-point Sort<br>Indices `1`: `1:` The size of the bit-vector to convert to.</sub> | `((_ fp.to_ubv 4) RTZ three)` → `#b0011` |
| `FLOATINGPOINT_TO_SBV` | `fp.to_sbv` | Float to signed bit-vector of width `w`.<br><sub>Arity `2`: `1:` Term of Sort RoundingMode; `2:` Term of floating-point Sort<br>Indices `1`: `1:` The size of the bit-vector to convert to.</sub> | `((_ fp.to_sbv 4) RTZ m1)` → `#b1111` |
| `FLOATINGPOINT_TO_REAL` | `fp.to_real` | The exact real value of a float (unspecified for infinities and NaN).<br><sub>Arity `1`: `1:` Term of Sort Real</sub> | `(fp.to_real h)` → `0.5` |

## Arrays

Arrays are total maps `(Array I E)` from an index sort to an element sort, with no bounds. `select` reads and `store` writes (returning a new array). Two arrays are equal exactly when they agree at every index (extensionality). This project's `ARR-*` encodings use this theory.

**Logic:** `A` (or `AX`)

The examples in this section assume:

```smt2
(declare-const a (Array Int Int))
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `SELECT` | `select` | Reads `a[i]`.<br><sub>Arity `2`: `1:` Term of array Sort; `2:` Term of array index Sort</sub> | `(select (store a 1 42) 1)` → `42` |
| `STORE` | `store` | `a` with index `i` set to `v`; every other index is unchanged. This project's `ARR-EXP` / `ARR-INL` chains are built from stores.<br><sub>Arity `3`: `1:` Term of array Sort; `2:` Term of array index Sort; `3:` Term of array element Sort</sub> | `(select (store a 1 42) 2)` → `(select a 2)` |
| `CONST_ARRAY` | `((as const (Array I E)) v)` | The array with the same value at every index. This cvc5 build needs `--arrays-exp` to solve with it.<br><sub>Arity `2`: `1:` Term of array Sort; `2:` Term of array element Sort (value)</sub> | `(select ((as const (Array Int Int)) 0) 7)` → `0` <sub>(`--arrays-exp`)</sub> |
| `EQ_RANGE` | `eqrange` | `(eqrange a b i j)`: arrays `a` and `b` agree on every index from `i` to `j` (inclusive). Experimental; needs `--arrays-exp`. | `(eqrange a (store a 5 0) 1 4)` → `true` <sub>(`--arrays-exp`)</sub> |

## Datatypes

Algebraic datatypes: enumerations, records, lists, trees. Each datatype has constructors (with selector fields); values built by different constructors are always different, and every value is built by exactly one constructor. Tuples and `Nullable` are built-in datatypes. This project's `LIST-DT` encoding uses an enumeration datatype.

**Logic:** `DT`

The examples in this section assume:

```smt2
(declare-datatype Color ((Red) (Green) (Blue)))
(declare-datatype IntList ((nil) (cons (head Int) (tail IntList))))
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `APPLY_CONSTRUCTOR` | `tuple`, `nullable.some` | Builds a value with a constructor. Values from different constructors are always distinct, so `Red`, `Green`, `Blue` need no `distinct` assertion. `tuple` and `nullable.some` are built-in constructors.<br><sub>Arity `n > 0`: `1:` DatatypeConstructor Term (see DatatypeConstructor::getTerm() const); `2..n:` Terms of the Sorts of the selectors of the constructor (the arguments to the constructor)</sub> | `(distinct Red Green Blue)` → `true` |
| `APPLY_SELECTOR` | `nullable.val` | Reads a constructor field. Applied to the wrong constructor (like `(head nil)`) it gives an unknown value.<br><sub>Arity `2`: `1:` DatatypeSelector Term (see DatatypeSelector::getTerm() const); `2:` Term of the codomain Sort of the selector</sub> | `(head (cons 1 nil))` → `1` |
| `APPLY_TESTER` | `is`, `nullable.is_null`, `nullable.is_some` | `((_ is c) x)`: whether `x` was built by constructor `c`.<br><sub>Arity `2`: `1:` Datatype tester Term (see DatatypeConstructor::getTesterTerm() const); `2:` Term of Datatype Sort (DatatypeConstructor must belong to this Datatype Sort)</sub> | `((_ is cons) (cons 1 nil))` → `true` |
| `APPLY_UPDATER` | `update` | `((_ update field) x v)`: a copy of `x` with one field replaced (unchanged if `x` has no such field).<br><sub>Arity `3`: `1:` Datatype updater Term (see DatatypeSelector::getUpdaterTerm() const); `2:` Term of Datatype Sort (DatatypeSelector of the updater must belong to a constructor of this Datatype Sort); `3:` Term of the codomain Sort of the selector (the Term to update the field of the datatype term with)</sub> | `((_ update head) (cons 1 nil) 5)` → `(cons 5 nil)` |
| `MATCH` | `match` | Pattern matching on constructors, like `match` in functional languages. | `(match (cons 7 nil) ((nil 0) ((cons h t) h)))` → `7` |
| `MATCH_CASE` |  | One case of a `match` for a constructor without fields (`(nil 0)` above). Only used when building `match` terms in C++. |  |
| `MATCH_BIND_CASE` |  | One case of a `match` that binds variables to the fields (`((cons h t) h)` above). Only used when building `match` terms in C++. |  |
| `TUPLE_PROJECT` | `tuple.project` | Keeps the listed positions of a tuple, in the given order.<br><sub>Arity `1`: `1:` Term of tuple Sort<br>Indices `n`: `1..n:` The tuple indices to project</sub> | `((_ tuple.project 0 2) (tuple 1 true 3))` → `(tuple 1 3)` |
| `NULLABLE_LIFT` | `nullable.lift` | Applies an operator to nullable values, giving null if any argument is null (SQL-style). `(Nullable T)` has values `nullable.null` and `(nullable.some x)`.<br><sub>Arity `n > 1`: `1..n:` Terms of nullable sort</sub><br><sub>C++: `TermManager::mkNullableLift(Kind, const std::vector<Term>&)`</sub> | `((_ nullable.lift +) (nullable.some 1) (nullable.some 2))` → `(nullable.some 3)` |

## Separation logic

Separation logic reasons about a heap of memory cells. `declare-heap` fixes the location and data sorts. Formulas describe parts of the heap: `(pto l v)` is a heap with exactly one cell `l` holding `v`, and `(sep P Q)` splits the heap into two *disjoint* parts satisfying P and Q. The examples are scripts (the expected result is shown).

**Logic:** `SEP_` prefix or `ALL`

The examples in this section assume:

```smt2
(declare-heap (Int Int))
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `SEP_NIL` | `sep.nil` | The null location; it can never be allocated.<br><sub>C++: `TermManager::mkSepNil(const Sort&)`</sub> | `(assert (pto (as sep.nil Int) 5))`<br>→ `unsat` |
| `SEP_EMP` | `sep.emp` | The empty heap: holds only when no cell is allocated.<br><sub>C++: `TermManager::mkSepEmp()`</sub> | `(assert (and sep.emp (pto 1 10)))`<br>→ `unsat` |
| `SEP_PTO` | `pto` | `(pto l v)`: the heap is exactly one cell, at location `l`, holding `v`.<br><sub>Arity `2`: `1:` Term denoting the location of the points-to constraint; `2:` Term denoting the data of the points-to constraint</sub> | `(assert (pto 1 10))`<br>`(assert (pto 1 20))`<br>→ `unsat` |
| `SEP_STAR` | `sep` | Separating conjunction: the heap splits into disjoint parts, one per argument. Two cells at the same location cannot be disjoint.<br><sub>Arity `n > 1`: `1..n:` Terms of sort Bool (the child constraints that hold in; disjoint (separated) heaps)</sub> | `(assert (sep (pto 1 10) (pto 1 20)))`<br>→ `unsat` |
| `SEP_WAND` | `wand` | Magic wand `(wand P Q)`: adding any disjoint heap satisfying `P` to the current heap gives one satisfying `Q`.<br><sub>Arity `2`: `1:` Terms of Sort Bool (the antecendant of the magic wand constraint); `2:` Terms of Sort Bool (conclusion of the magic wand constraint,; which is asserted to hold in all heaps that are disjoint; extensions of the antecedent)</sub> | `(assert (wand (pto 1 10) (sep (pto 1 10) (pto 2 20))))`<br>`(assert (pto 2 20))`<br>→ `sat` |

## Finite sets

Finite sets `(Set T)` of any element sort. The core (`union`, `inter`, `minus`, `member`, `subset`, `singleton`, `card`) is decidable; the higher-order operators (`set.map`, `set.filter`, `set.fold`, ...) need `--sets-exp` and may answer `unknown`. This project's `SET-*` encodings use this theory.

**Logic:** `FS`

The examples in this section assume:

```smt2
(define-fun A () (Set Int) (set.insert 1 2 (set.singleton 3)))
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `SET_EMPTY` | `(as set.empty (Set T))` | The empty set (the element sort must be given with `as`).<br><sub>C++: `TermManager::mkEmptySet(const Sort&)`</sub> | `(set.card (as set.empty (Set Int)))` → `0` |
| `SET_UNION` | `set.union` | Union.<br><sub>Arity `2`: `1..2:` Terms of set Sort</sub> | `(set.union (set.singleton 1) (set.singleton 2))` → `(set.insert 1 (set.singleton 2))` |
| `SET_INTER` | `set.inter` | Intersection.<br><sub>Arity `2`: `1..2:` Terms of set Sort</sub> | `(set.inter A (set.insert 3 4 (set.singleton 5)))` → `(set.singleton 3)` |
| `SET_MINUS` | `set.minus` | Difference: elements of the first set not in the second.<br><sub>Arity `2`: `1..2:` Terms of set Sort</sub> | `(set.minus A (set.singleton 1))` → `(set.insert 2 (set.singleton 3))` |
| `SET_SUBSET` | `set.subset` | Whether the first set is a subset of the second.<br><sub>Arity `2`: `1..2:` Terms of set Sort</sub> | `(set.subset (set.singleton 1) A)` → `true` |
| `SET_MEMBER` | `set.member` | Membership. This project's `SET-MEM` encoding is `(set.member x {1..K})`.<br><sub>Arity `2`: `1:` Term of any Sort (must match the element Sort of the given set Term); `2:` Term of set Sort</sub> | `(set.member 2 A)` → `true` |
| `SET_SINGLETON` | `set.singleton` | The set with one element.<br><sub>Arity `1`: `1:` Term of any Sort (the set element)</sub> | `(set.card (set.singleton 7))` → `1` |
| `SET_INSERT` | `set.insert` | `(set.insert e1 ... en S)`: `S` with the elements added. Handy for writing set literals.<br><sub>Arity `n > 0`: `1..n-1:` Terms of any Sort (must match the element sort of the given set Term); `n:` Term of set Sort</sub> | `(set.card (set.insert 1 2 (set.singleton 3)))` → `3` |
| `SET_CARD` | `set.card` | Number of elements. Mixing cardinality with arithmetic needs `LIA` in the logic (e.g. `QF_FSLIA`).<br><sub>Arity `1`: `1:` Term of set Sort</sub> | `(set.card A)` → `3` |
| `SET_COMPLEMENT` | `set.complement` | All elements of the universe (`set.universe`) not in the set. Needs `--sets-exp`. See the caveat on `SET_UNIVERSE`.<br><sub>Arity `1`: `1:` Term of set Sort</sub> | `(set.member 4 (set.union A (set.complement A)))` → `true` <sub>(`--sets-exp`)</sub> ⚠ *cvc5 could not prove this (answered sat)* |
| `SET_UNIVERSE` | `(as set.universe (Set T))` | Meant as the set of all values of the element sort. Needs `--sets-exp`. Caveat: in this build cvc5 does not force the universe to contain every value; asked for a model, it may even make it empty, so even this example is not proven.<br><sub>C++: `TermManager::mkUniverseSet(const Sort&)`</sub> | `(set.card (as set.universe (Set Bool)))` → `2` <sub>(`--sets-exp`)</sub> ⚠ *cvc5 could not prove this (answered sat)* |
| `SET_COMPREHENSION` | `set.comprehension` | `{ x \| P(x) }`, the set of values satisfying a predicate (it must be finite). Needs `--sets-exp`. | `(set.comprehension ((x Int)) (and (> x 0) (< x 4)) x)` → `A` <sub>(`--sets-exp`)</sub> |
| `SET_CHOOSE` | `set.choose` | Some element of a non-empty set (unspecified which).<br><sub>Arity `1`: `1:` Term of set Sort</sub> | `(set.member (set.choose A) A)` → `true` <sub>(`--sets-exp`)</sub> |
| `SET_IS_EMPTY` | `set.is_empty` | Whether the set is empty.<br><sub>Arity `1`: `1:` Term of set Sort</sub> | `(set.is_empty A)` → `false` |
| `SET_IS_SINGLETON` | `set.is_singleton` | Whether the set has exactly one element.<br><sub>Arity `1`: `1:` Term of set Sort</sub> | `(set.is_singleton (set.singleton 1))` → `true` |
| `SET_MAP` | `set.map` | Applies a function to every element (duplicates merge). | `(set.map (lambda ((x Int)) (* 2 x)) A)` → `(set.insert 2 4 (set.singleton 6))` <sub>(logic `HO_ALL`)</sub> <sub>(`--sets-exp`)</sub> |
| `SET_FILTER` | `set.filter` | Keeps the elements satisfying a predicate. | `(set.filter (lambda ((x Int)) (> x 1)) A)` → `(set.insert 2 (set.singleton 3))` <sub>(logic `HO_ALL`)</sub> <sub>(`--sets-exp`)</sub> |
| `SET_ALL` | `set.all` | Whether every element satisfies a predicate. | `(set.all (lambda ((x Int)) (> x 0)) A)` → `true` <sub>(logic `HO_ALL`)</sub> <sub>(`--sets-exp`)</sub> |
| `SET_SOME` | `set.some` | Whether some element satisfies a predicate. | `(set.some (lambda ((x Int)) (> x 2)) A)` → `true` <sub>(logic `HO_ALL`)</sub> <sub>(`--sets-exp`)</sub> |
| `SET_FOLD` | `set.fold` | `(set.fold f init S)`: combines the elements with `f` (element, accumulator), starting from `init`. `f` should not depend on the order. | `(set.fold (lambda ((x Int) (acc Int)) (+ x acc)) 0 A)` → `6` <sub>(logic `HO_ALL`)</sub> <sub>(`--sets-exp`)</sub> |

## Relations

A relation `(Relation T1 ... Tn)` is a set of tuples, `(Set (Tuple T1 ... Tn))`, with database-style operators. Column indices start at 0.

**Logic:** `FS` (with `DT` for tuples) or `ALL`

The examples in this section assume:

```smt2
(define-fun R () (Relation Int Int) (set.insert (tuple 1 2) (set.singleton (tuple 2 3))))
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `RELATION_JOIN` | `rel.join` | Relational composition: `(x, y)` and `(y, z)` give `(x, z)`; the last column of the first relation is matched with the first column of the second and both are dropped.<br><sub>Arity `2`: `1..2:` Terms of relation Sort</sub> | `(rel.join R R)` → `(set.singleton (tuple 1 3))` |
| `RELATION_TABLE_JOIN` | `rel.table_join` | `((_ rel.table_join m1 n1 ...) A B)`: SQL-style join; pairs of tuples where column `m_i` of A equals column `n_i` of B, keeping all columns. | `((_ rel.table_join 1 0) R R)` → `(set.singleton (tuple 1 2 2 3))` <sub>(`--sets-exp`)</sub> |
| `RELATION_PRODUCT` | `rel.product` | Cartesian product: every tuple of the first concatenated with every tuple of the second.<br><sub>Arity `2`: `1..2:` Terms of relation Sort</sub> | `(set.card (rel.product R R))` → `4` |
| `RELATION_TRANSPOSE` | `rel.transpose` | Reverses every tuple.<br><sub>Arity `1`: `1:` Term of relation Sort</sub> | `(rel.transpose R)` → `(set.insert (tuple 2 1) (set.singleton (tuple 3 2)))` |
| `RELATION_TCLOSURE` | `rel.tclosure` | Transitive closure of a binary relation.<br><sub>Arity `1`: `1:` Term of relation Sort</sub> | `(rel.tclosure R)` → `(set.insert (tuple 1 2) (tuple 2 3) (set.singleton (tuple 1 3)))` |
| `RELATION_JOIN_IMAGE` | `rel.join_image` | `(rel.join_image R n)`: the 1-tuples `(x)` such that `x` is related by binary relation `R` to at least `n` distinct values. Experimental.<br><sub>Arity `2`: `1..2:` Terms of relation Sort</sub> | `(rel.join_image (set.insert (tuple 1 2) (tuple 1 3) (set.singleton (tuple 2 3))) 2)` → `(set.singleton (tuple 1))` |
| `RELATION_IDEN` | `rel.iden` | The identity relation `{(x, x)}` on a set of 1-tuples.<br><sub>Arity `1`: `1:` Term of relation Sort</sub> | `(rel.iden (set.singleton (tuple 1)))` → `(set.singleton (tuple 1 1))` |
| `RELATION_GROUP` | `rel.group` | `((_ rel.group n1 ...) A)`: splits `A` into parts whose tuples agree on the given columns. Returns a set of relations. Experimental. | `(set.card ((_ rel.group 0) (set.insert (tuple 1 2) (tuple 1 3) (set.singleton (tuple 2 3)))))` → `2` <sub>(`--sets-exp`)</sub> |
| `RELATION_AGGREGATE` | `rel.aggr` | `((_ rel.aggr n1 ...) f init A)`: groups `A` by the given columns and folds each group with `f`. Returns a set of results. Experimental. | `((_ rel.aggr 0) (lambda ((t (Tuple Int Int)) (acc Int)) (+ ((_ tuple.select 1) t) acc)) 0 (set.insert (tuple 1 2) (tuple 1 3) (set.singleton (tuple 2 3))))` → `(set.insert 5 (set.singleton 3))` <sub>(logic `HO_ALL`)</sub> <sub>(`--sets-exp`)</sub> |
| `RELATION_PROJECT` | `rel.project` | Keeps the given columns of every tuple (duplicates merge).<br><sub>Arity `1`: `1:` Term of relation Sort<br>Indices `n`: `1..n:` Indices of the projection</sub> | `((_ rel.project 0) R)` → `(set.insert (tuple 1) (set.singleton (tuple 2)))` |

## Bags (multisets)

A bag (multiset) `(Bag T)` is like a set, but each element has a multiplicity (how many times it is in the bag). `(bag x n)` is the bag with `n` copies of `x`. A *table* `(Table T1 ... Tn)` is a bag of tuples (SQL semantics, duplicates allowed). Needs logic `ALL`.

**Logic:** `ALL`

The examples in this section assume:

```smt2
(define-fun B () (Bag Int) (bag.union_disjoint (bag 1 2) (bag 2 1)))
(define-fun C () (Bag Int) (bag.union_disjoint (bag 1 1) (bag 3 1)))
(define-fun T () (Table Int Int) (bag.union_disjoint (bag (tuple 1 2) 1) (bag (tuple 2 3) 1)))
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `BAG_EMPTY` | `(as bag.empty (Bag T))` | The empty bag.<br><sub>C++: `TermManager::mkEmptyBag(const Sort&)`</sub> | `(bag.card (as bag.empty (Bag Int)))` → `0` |
| `BAG_UNION_MAX` | `bag.union_max` | Union taking the *larger* multiplicity of each element.<br><sub>Arity `2`: `1..2:` Terms of bag Sort</sub> | `(bag.count 1 (bag.union_max B C))` → `2` |
| `BAG_UNION_DISJOINT` | `bag.union_disjoint` | Union *adding* multiplicities.<br><sub>Arity `2`: `1..2:` Terms of bag Sort</sub> | `(bag.count 1 (bag.union_disjoint B C))` → `3` |
| `BAG_INTER_MIN` | `bag.inter_min` | Intersection taking the smaller multiplicity.<br><sub>Arity `2`: `1..2:` Terms of bag Sort</sub> | `(bag.count 1 (bag.inter_min B C))` → `1` |
| `BAG_DIFFERENCE_SUBTRACT` | `bag.difference_subtract` | Subtracts multiplicities (never below 0).<br><sub>Arity `2`: `1..2:` Terms of bag Sort</sub> | `(bag.count 1 (bag.difference_subtract B C))` → `1` |
| `BAG_DIFFERENCE_REMOVE` | `bag.difference_remove` | Removes every element of the second bag entirely from the first.<br><sub>Arity `2`: `1..2:` Terms of bag Sort</sub> | `(bag.count 1 (bag.difference_remove B C))` → `0` |
| `BAG_SUBBAG` | `bag.subbag` | Whether every multiplicity in the first bag is `<=` the one in the second.<br><sub>Arity `2`: `1..2:` Terms of bag Sort</sub> | `(bag.subbag (bag 1 1) B)` → `true` |
| `BAG_COUNT` | `bag.count` | Multiplicity of an element (0 if absent). | `(bag.count 2 B)` → `1` |
| `BAG_MEMBER` | `bag.member` | Whether the element occurs at least once.<br><sub>Arity `2`: `1:` Term of any Sort (must match the element Sort of the given bag Term); `2:` Terms of bag Sort</sub> | `(bag.member 3 B)` → `false` |
| `BAG_SETOF` | `bag.setof` | Same elements, each with multiplicity 1.<br><sub>Arity `1`: `1:` Term of bag Sort</sub> | `(bag.count 1 (bag.setof B))` → `1` |
| `BAG_MAKE` | `bag` | `(bag x n)`: `n` copies of `x` (empty if `n <= 0`).<br><sub>Arity `2`: `1:` Term of any Sort (the bag element); `2:` Term of Sort Int (the multiplicity of the element)</sub> | `(bag.count 4 (bag 4 3))` → `3` |
| `BAG_CARD` | `bag.card` | Total number of elements, counting multiplicity.<br><sub>Arity `1`: `1:` Term of bag Sort</sub> | `(bag.card B)` → `3` |
| `BAG_CHOOSE` | `bag.choose` | Some element of a non-empty bag.<br><sub>Arity `1`: `1:` Term of bag Sort</sub> | `(bag.member (bag.choose B) B)` → `true` |
| `BAG_MAP` | `bag.map` | Applies a function to every element, keeping multiplicities (results add up). | `(bag.count 0 (bag.map (lambda ((x Int)) 0) B))` → `3` <sub>(logic `HO_ALL`)</sub> |
| `BAG_FILTER` | `bag.filter` | Keeps the elements satisfying a predicate, with their multiplicities. | `(bag.filter (lambda ((x Int)) (> x 1)) B)` → `(bag 2 1)` <sub>(logic `HO_ALL`)</sub> |
| `BAG_ALL` | `bag.all` | Whether every element satisfies a predicate. | `(bag.all (lambda ((x Int)) (> x 0)) B)` → `true` <sub>(logic `HO_ALL`)</sub> |
| `BAG_SOME` | `bag.some` | Whether some element satisfies a predicate. | `(bag.some (lambda ((x Int)) (> x 1)) B)` → `true` <sub>(logic `HO_ALL`)</sub> |
| `BAG_FOLD` | `bag.fold` | `(bag.fold f init B)`: combines all elements, each as many times as its multiplicity. | `(bag.fold (lambda ((x Int) (acc Int)) (+ x acc)) 0 B)` → `4` <sub>(logic `HO_ALL`)</sub> |
| `BAG_PARTITION` | `bag.partition`, `table.group` | `(bag.partition r B)`: splits `B` into the classes of the equivalence relation `r`. Returns a bag of bags. Experimental. | `(bag.card (bag.partition (lambda ((x Int) (y Int)) (= (mod x 2) (mod y 2))) (bag.union_disjoint (bag 1 1) (bag 2 1) (bag 3 1))))` → `2` <sub>(logic `HO_ALL`)</sub> |
| `TABLE_PRODUCT` | `table.product` | Cartesian product of two tables.<br><sub>Arity `2`: `1..2:` Terms of table Sort</sub> | `(bag.card (table.product T T))` → `4` |
| `TABLE_PROJECT` | `table.project` | Keeps the given columns of every row (duplicates are kept, as in SQL).<br><sub>Arity `1`: `1:` Term of table Sort<br>Indices `n`: `1..n:` Indices of the projection</sub> | `((_ table.project 0) T)` → `(bag.union_disjoint (bag (tuple 1) 1) (bag (tuple 2) 1))` |
| `TABLE_AGGREGATE` | `table.aggr` | `((_ table.aggr n1 ...) f init A)`: SQL `GROUP BY` on the given columns (at least one) followed by an aggregate `f`. Returns a bag with one result per group. | `((_ table.aggr 0) (lambda ((t (Tuple Int Int)) (acc Int)) (+ ((_ tuple.select 1) t) acc)) 0 T)` → `(bag.union_disjoint (bag 2 1) (bag 3 1))` <sub>(logic `HO_ALL`)</sub> |
| `TABLE_JOIN` | `table.join` | `((_ table.join m1 n1 ...) A B)`: SQL inner join on column `m_i` of A = column `n_i` of B. | `((_ table.join 1 0) T T)` → `(bag (tuple 1 2 2 3) 1)` |
| `TABLE_GROUP` | `table.group` | `((_ table.group n1 ...) A)`: splits a table into parts whose rows agree on the given columns (SQL `GROUP BY` without aggregating). | `(bag.card ((_ table.group 1) (bag.union_disjoint (bag (tuple 1 5) 1) (bag (tuple 2 5) 1))))` → `1` |

## Strings, sequences and regular expressions

Unicode strings, generic sequences `(Seq T)`, and regular expressions (`RegLan`). Positions start at 0. Most functions are total: out-of-range arguments give a default (`""`, `-1`) instead of an error. Use logic `S` for pure strings and `SLIA` when lengths and integer conversions appear. This project's `STRING` and `STR-*` encodings use this theory.

**Logic:** `S` (`SLIA` with length/integer functions)

The examples in this section assume:

```smt2
(define-fun S () (Seq Int) (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)))
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `STRING_CONCAT` | `str.++` | Concatenation.<br><sub>Arity `n > 1`: `1..n:` Terms of Sort String</sub> | `(str.++ "ab" "cd")` → `"abcd"` |
| `STRING_IN_REGEXP` | `str.in_re` | Whether a string matches a regular expression. This project's `STR-REG` encoding.<br><sub>Arity `2`: `1:` Term of Sort String; `2:` Term of Sort RegLan</sub> | `(str.in_re "abc" (re.* (re.range "a" "c")))` → `true` |
| `STRING_LENGTH` | `str.len` | Number of characters. This project's `STR-LEX` uses `(= (str.len x) 1)`.<br><sub>Arity `1`: `1:` Term of Sort String</sub> | `(str.len "hello")` → `5` |
| `STRING_SUBSTR` | `str.substr` | `(str.substr s i n)`: up to `n` characters starting at position `i` (`""` if out of range). | `(str.substr "hello" 1 3)` → `"ell"` |
| `STRING_UPDATE` | `str.update` | `(str.update s i t)`: overwrites `s` from position `i` with `t`, keeping the length. | `(str.update "hello" 0 "J")` → `"Jello"` |
| `STRING_CHARAT` | `str.at` | The character at a position, as a string of length 1 (`""` if out of range). | `(str.at "hello" 1)` → `"e"` |
| `STRING_CONTAINS` | `str.contains` | Whether the second string occurs inside the first. This project's `STR-SUB` encoding. | `(str.contains "hello" "ell")` → `true` |
| `STRING_INDEXOF` | `str.indexof` | `(str.indexof s t i)`: first position `>= i` where `t` occurs, or -1. | `(str.indexof "hello" "l" 0)` → `2` |
| `STRING_INDEXOF_RE` | `str.indexof_re` | First position `>= i` where a match of the regex starts, or -1. | `(str.indexof_re "a1b2" (re.range "0" "9") 0)` → `1` |
| `STRING_REPLACE` | `str.replace` | Replaces the *first* occurrence. | `(str.replace "hello" "l" "L")` → `"heLlo"` |
| `STRING_REPLACE_ALL` | `str.replace_all` | Replaces every occurrence. | `(str.replace_all "hello" "l" "L")` → `"heLLo"` |
| `STRING_REPLACE_RE` | `str.replace_re` | Replaces the first (shortest leftmost) regex match. | `(str.replace_re "a1b2" (re.range "0" "9") "#")` → `"a#b2"` |
| `STRING_REPLACE_RE_ALL` | `str.replace_re_all` | Replaces every regex match. | `(str.replace_re_all "a1b2" (re.range "0" "9") "#")` → `"a#b#"` |
| `STRING_TO_LOWER` | `str.to_lower` | Lower-cases ASCII letters.<br><sub>Arity `1`: `1:` Term of Sort String</sub> | `(str.to_lower "HeLLo")` → `"hello"` |
| `STRING_TO_UPPER` | `str.to_upper` | Upper-cases ASCII letters.<br><sub>Arity `1`: `1:` Term of Sort String</sub> | `(str.to_upper "HeLLo")` → `"HELLO"` |
| `STRING_REV` | `str.rev` | Reverses the string.<br><sub>Arity `1`: `1:` Term of Sort String</sub> | `(str.rev "abc")` → `"cba"` |
| `STRING_TO_CODE` | `str.to_code` | Code point of a one-character string; -1 for any other length.<br><sub>Arity `1`: `1:` Term of Sort String</sub> | `(str.to_code "A")` → `65` |
| `STRING_FROM_CODE` | `str.from_code` | The one-character string with a code point (`""` if invalid).<br><sub>Arity `1`: `1:` Term of Sort Int</sub> | `(str.from_code 66)` → `"B"` |
| `STRING_LT` | `str.<` | Lexicographic `<` (by code point). | `(str.< "abc" "abd")` → `true` |
| `STRING_LEQ` | `str.<=` | Lexicographic `<=`. This project's `STR-LEX` bounds. | `(str.<= "b" "ab")` → `false` |
| `STRING_PREFIX` | `str.prefixof` | `(str.prefixof t s)`: whether `t` is a prefix of `s`. Note the order: the prefix comes first. | `(str.prefixof "he" "hello")` → `true` |
| `STRING_SUFFIX` | `str.suffixof` | `(str.suffixof t s)`: whether `t` is a suffix of `s`. | `(str.suffixof "lo" "hello")` → `true` |
| `STRING_IS_DIGIT` | `str.is_digit` | Whether the string is a single character `0`-`9`.<br><sub>Arity `1`: `1:` Term of Sort String</sub> | `(str.is_digit "7")` → `true` |
| `STRING_FROM_INT` | `str.from_int` | Decimal spelling of a non-negative integer (`""` for negatives).<br><sub>Arity `1`: `1:` Term of Sort Int</sub> | `(str.from_int 42)` → `"42"` |
| `STRING_TO_INT` | `str.to_int` | Reads a string of decimal digits (leading zeros allowed); -1 if it is empty or has a non-digit. This project's `STR-INT` encoding.<br><sub>Arity `1`: `1:` Term of Sort Int</sub> | `(str.to_int "042")` → `42` |
| `CONST_STRING` | `"abc"` | A string literal. A quote inside is written `""`; other characters can be written `\u{...}` by code point.<br><sub>C++: `TermManager::mkString(const std::string&, bool)`<br>`TermManager::mkString(const std::u32string&)`</sub> | `(str.len "a""b")` → `3` |
| `STRING_TO_REGEXP` | `str.to_re` | The regex matching exactly one string.<br><sub>Arity `1`: `1:` Term of Sort String</sub> | `(str.in_re "ab" (str.to_re "ab"))` → `true` |
| `REGEXP_CONCAT` | `re.++` | Regex concatenation.<br><sub>Arity `2`: `1..2:` Terms of Sort RegLan</sub> | `(str.in_re "ab" (re.++ (str.to_re "a") (str.to_re "b")))` → `true` |
| `REGEXP_UNION` | `re.union` | Matches if any part matches (`\|`).<br><sub>Arity `2`: `1..2:` Terms of Sort RegLan</sub> | `(str.in_re "b" (re.union (str.to_re "a") (str.to_re "b")))` → `true` |
| `REGEXP_INTER` | `re.inter` | Matches if all parts match.<br><sub>Arity `2`: `1..2:` Terms of Sort RegLan</sub> | `(str.in_re "b" (re.inter (re.range "a" "c") (re.range "b" "d")))` → `true` |
| `REGEXP_DIFF` | `re.diff` | Matches the first regex but not the second.<br><sub>Arity `2`: `1..2:` Terms of Sort RegLan</sub> | `(str.in_re "b" (re.diff (re.range "a" "c") (str.to_re "b")))` → `false` |
| `REGEXP_STAR` | `re.*` | Zero or more repetitions (`*`).<br><sub>Arity `1`: `1:` Term of Sort RegLan</sub> | `(str.in_re "" (re.* (str.to_re "a")))` → `true` |
| `REGEXP_PLUS` | `re.+` | One or more repetitions (`+`).<br><sub>Arity `1`: `1:` Term of Sort RegLan</sub> | `(str.in_re "" (re.+ (str.to_re "a")))` → `false` |
| `REGEXP_OPT` | `re.opt` | Zero or one occurrence (`?`).<br><sub>Arity `1`: `1:` Term of Sort RegLan</sub> | `(str.in_re "" (re.opt (str.to_re "a")))` → `true` |
| `REGEXP_RANGE` | `re.range` | Any single character between two characters (`[a-z]`).<br><sub>Arity `2`: `1:` Term of Sort String (lower bound character for the range); `2:` Term of Sort String (upper bound character for the range)</sub> | `(str.in_re "m" (re.range "a" "z"))` → `true` |
| `REGEXP_REPEAT` | `re.^` | Exactly `n` repetitions (`{n}`).<br><sub>Arity `1`: `1:` Term of Sort RegLan<br>Indices `1`: `1:` The number of repetitions</sub> | `(str.in_re "abab" ((_ re.^ 2) (str.to_re "ab")))` → `true` |
| `REGEXP_LOOP` | `re.loop` | Between `lo` and `hi` repetitions (`{lo,hi}`).<br><sub>Arity `1`: `1:` Term of Sort RegLan<br>Indices `1`: `1:` The lower bound; `2:` The upper bound</sub> | `(str.in_re "aaa" ((_ re.loop 2 4) (str.to_re "a")))` → `true` |
| `REGEXP_NONE` | `re.none` | Matches nothing.<br><sub>C++: `TermManager::mkRegexpNone()`</sub> | `(str.in_re "a" re.none)` → `false` |
| `REGEXP_ALL` | `re.all` | Matches every string (`.*`).<br><sub>C++: `TermManager::mkRegexpAll()`</sub> | `(str.in_re "anything" re.all)` → `true` |
| `REGEXP_ALLCHAR` | `re.allchar` | Matches any single character (`.`).<br><sub>C++: `TermManager::mkRegexpAllchar()`</sub> | `(str.in_re "ab" re.allchar)` → `false` |
| `REGEXP_COMPLEMENT` | `re.comp` | Matches exactly the strings the regex does not.<br><sub>Arity `1`: `1:` Term of Sort RegLan</sub> | `(str.in_re "a" (re.comp (str.to_re "a")))` → `false` |
| `SEQ_CONCAT` | `seq.++` | Concatenation of sequences.<br><sub>Arity `n > 1`: `1..n:` Terms of sequence Sort</sub> | `(seq.len (seq.++ S S))` → `6` |
| `SEQ_LENGTH` | `seq.len` | Number of elements.<br><sub>Arity `1`: `1:` Term of sequence Sort</sub> | `(seq.len S)` → `3` |
| `SEQ_EXTRACT` | `seq.extract` | `(seq.extract s i n)`: up to `n` elements starting at position `i`. | `(seq.extract S 1 2)` → `(seq.++ (seq.unit 2) (seq.unit 3))` |
| `SEQ_UPDATE` | `seq.update` | Overwrites from a position, keeping the length. | `(seq.update S 0 (seq.unit 9))` → `(seq.++ (seq.unit 9) (seq.unit 2) (seq.unit 3))` |
| `SEQ_AT` | `seq.at` | The element at a position, as a length-1 sequence (empty if out of range). Compare `seq.nth`. | `(seq.at S 1)` → `(seq.unit 2)` |
| `SEQ_CONTAINS` | `seq.contains` | Whether the second sequence occurs contiguously in the first. | `(seq.contains S (seq.++ (seq.unit 2) (seq.unit 3)))` → `true` |
| `SEQ_INDEXOF` | `seq.indexof` | First position `>= i` of a subsequence, or -1. | `(seq.indexof S (seq.unit 3) 0)` → `2` |
| `SEQ_REPLACE` | `seq.replace` | Replaces the first occurrence. | `(seq.replace S (seq.unit 2) (seq.unit 7))` → `(seq.++ (seq.unit 1) (seq.unit 7) (seq.unit 3))` |
| `SEQ_REPLACE_ALL` | `seq.replace_all` | Replaces every occurrence. | `(seq.replace_all (seq.++ S S) (seq.unit 2) (seq.unit 0))` → `(seq.++ (seq.unit 1) (seq.unit 0) (seq.unit 3) (seq.unit 1) (seq.unit 0) (seq.unit 3))` |
| `SEQ_REV` | `seq.rev` | Reverses the sequence.<br><sub>Arity `1`: `1:` Term of sequence Sort</sub> | `(seq.rev S)` → `(seq.++ (seq.unit 3) (seq.unit 2) (seq.unit 1))` |
| `SEQ_PREFIX` | `seq.prefixof` | `(seq.prefixof t s)`: whether `t` is a prefix of `s`. | `(seq.prefixof (seq.unit 1) S)` → `true` |
| `SEQ_SUFFIX` | `seq.suffixof` | `(seq.suffixof t s)`: whether `t` is a suffix of `s`. | `(seq.suffixof (seq.unit 1) S)` → `false` |
| `CONST_SEQUENCE` | `(as seq.empty (Seq T))` | A constant sequence; in SMT-LIB written with `seq.empty` and `seq.unit`.<br><sub>C++: `TermManager::mkEmptySequence(const Sort&)`</sub> | `(seq.len (as seq.empty (Seq Int)))` → `0` |
| `SEQ_UNIT` | `seq.unit` | The sequence with one element.<br><sub>Arity `1`: `1:` Term of any Sort (the element term)</sub> | `(seq.nth (seq.unit 5) 0)` → `5` |
| `SEQ_NTH` | `seq.nth` | The element itself at a position (unknown value if out of range). | `(seq.nth S 1)` → `2` |

## Quantifiers

`forall` and `exists` over any sort. With quantifiers the problem is undecidable in general; cvc5 instantiates them using triggers (E-matching), conflict-based and enumerative instantiation, and may answer `unknown`. Drop the `QF_` prefix from the logic to allow them. Annotations (`!` with `:pattern`, `:qid`, ...) guide instantiation.

**Logic:** drop the `QF_` prefix

The examples in this section assume:

```smt2
(declare-fun f (Int) Int)
```

| Kind | SMT-LIB | What it does | Example |
|---|---|---|---|
| `FORALL` | `forall` | Holds when the body is true for every value of the bound variables. | `(forall ((x Int)) (> (+ x 1) x))` → `true` |
| `EXISTS` | `exists` | Holds when the body is true for some value. | `(exists ((x Int)) (= (* 2 x) 10))` → `true` |
| `VARIABLE_LIST` |  | The list of bound variables, `((x Int) (y Int))`. In C++ it is the first child of a `FORALL`/`EXISTS`/`LAMBDA`. | C++: `tm.mkTerm(cvc5::Kind::FORALL, {tm.mkTerm(cvc5::Kind::VARIABLE_LIST, {x}), body})` |
| `INST_PATTERN` |  | A trigger: `:pattern ((f x))` tells E-matching to instantiate the quantifier for each term `(f t)` it sees.<br><sub>Arity `n > 0`: `1..n:` Terms of any Sort</sub> | `(assert (forall ((x Int)) (! (= (f x) (+ x 1)) :pattern ((f x)))))`<br>`(assert (= (f 3) 5))`<br>→ `unsat` |
| `INST_NO_PATTERN` |  | `:no-pattern t`: never use `t` as a trigger.<br><sub>Arity `1`: `1:` Term of any Sort</sub> | `(assert (forall ((x Int)) (! (= (f x) (+ x 1)) :no-pattern (f (+ x 1)))))`<br>`(assert (= (f 3) 5))`<br>→ `unsat` |
| `INST_POOL` |  | `:pool (P)`: instantiate the quantifier only with terms from the given pools (sets of terms), instead of triggers. cvc5-specific. |  |
| `INST_ADD_TO_POOL` |  | `:inst-add-to-pool`: whenever the quantifier is instantiated, add a term to a pool. cvc5-specific.<br><sub>Arity `2`: `1:` The Term whose free variables are bound by the quantified formula.; `2:` The pool to add to, whose Sort should be a set of elements that match the Sort of the first argument.</sub> |  |
| `SKOLEM_ADD_TO_POOL` |  | `:skolem-add-to-pool`: when the quantifier is Skolemized, add the Skolem term to a pool. cvc5-specific.<br><sub>Arity `2`: `1:` The Term whose free variables are bound by the quantified formula.; `2:` The pool to add to, whose Sort should be a set of elements that match the Sort of the first argument.</sub> |  |
| `INST_ATTRIBUTE` |  | Other attributes on a quantifier, such as `:qid name` (a name shown in statistics).<br><sub>Arity `n > 0`: `1:` Term of Kind `CONST_STRING` (the keyword of the attribute); `2...n:` Terms representing the values of the attribute</sub> | `(assert (forall ((x Int)) (! (> (+ x 1) x) :qid succ_gt)))`<br>→ `sat` |
| `INST_PATTERN_LIST` |  | The list of annotations (patterns, attributes, pools) attached to a quantifier. In C++ it is the optional third child of `FORALL`/`EXISTS`. |  |
