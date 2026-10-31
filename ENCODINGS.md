# Encodings compared

Every encoding in this repository, side by side: which theory it uses, whether it is a **k-colorer** in the sense of Sebastiani's paper, what it puts on each node and each edge, how big the formula gets, and how well cvc5 and Z3 solve it. The details of each encoding are in the [README](README.md); this file is the overview.

## Notation

| Symbol | Meaning |
|---|---|
| n, m | number of nodes and edges of the graph |
| K | number of colors |
| w | bits needed for K values: `w = ⌈log₂ K⌉` |
| L | elements of a set or bag "universe": `L = ⌈log₂ K⌉` for the set encodings, the number of prime factors of K (with repetition) for `BAG-SUB` |
| e₁..e_K | the K distinct elements of the chosen element theory (theory-independent encodings) |

## What "k-colorer" means here

R. Sebastiani, *Colors Make Theories Hard* (IJCAR 2016), Definition 2. A **k-colorer** for a theory T is a formula `Colorer_k(v_i, c | y_i)` that is

- a **finite quantifier-free conjunction of T-literals** (a *cube*: no disjunctions, no quantifiers),
- over one **vertex variable** `v_i`, the **color variables** `c_1..c_k` (shared by all vertices), and **auxiliary variables** `y_i` that belong to vertex i only,

such that

1. it implies that the colors are pairwise different (`AllDifferent_k(c)`),
2. it implies that `v_i` equals one of the colors (`v_i = c_1 ∨ … ∨ v_i = c_k` is a *consequence*, not something written in the formula),
3. every one of the k choices `v_i = c_j` is possible with the same values for the colors.

The paper's reduction (Lemma 2) is then `⋀_i Colorer_k(v_i, c | y_i) ∧ ⋀_{(u,v) ∈ E} ¬(v_u = v_v)`: a conjunction of literals, which proves T-solving NP-hard for k ≥ 3 (Theorem 1). The colors may be fixed constants instead of variables (Remark 2), and a theory whose domain has exactly k elements needs no vertex literal at all: `AllDifferent_k(c)` alone is a k-colorer (Proposition 2). Property 1: a k-colorable theory is always **non-convex**.

So an encoding counts as a k-colorer when **(a)** each node's part is a cube that mentions only that node's variables, constants and the colors, **(b)** that cube allows exactly K values, and **(c)** each edge is `¬(u = v)`. The verdicts:

| Mark | Meaning |
|---|---|
| ✓ | a k-colorer as written |
| ✓ inl. | a k-colorer once a term is named: the node's color is a term over an auxiliary variable (`x mod K`, `2^e`, `A[i]`), and naming it `v_i` gives the paper's form exactly |
| ✓ P2 | Proposition 2: the sort itself has exactly K values (or is limited to K by a cardinality literal), so no vertex literal is needed |
| ◐ | the node part is a k-colorer, but the edges are not `¬(u = v)` (they mean the same on the K colors, and the paper's Definition 3 allows such an emulated disequality only when it works for every value) |
| ✗ | not a k-colorer, for the reason in the notes |

## The table

"Size" counts the asserted literals and clauses (the leading terms), plus anything unusual about term size. "Solved" is out of six instances, three SAT and three UNSAT (`myciel4` K = 5 / 4, `queen5_5` K = 5 / 4, `DSJC125.1` K = 5, `1-FullIns_4` K = 4), 30 s each; theory-independent encodings use their default element theory; "–" means the solver does not have the encoding.

### Integer arithmetic

| Encoding | Theory (logic) | k-colorer? | Variables per node | Node constraint | Edge constraint | Size | Solved cvc5 · Z3 |
|---|---|---|---|---|---|---|---|
| `LIA` | LIA (`QF_LIA`) | ✓ (the paper's Example 1) | 1 Int | `1 ≤ x ≤ K` (2 literals) | `x_u ≠ x_v` | 2n + m | 6 · 5 |
| `IDL` | difference logic (`QF_IDL`) | ✓ [1] | 1 Int, + 1 shared `zero` | `1 ≤ x − zero ≤ K` | `x_u ≠ x_v` | 2n + m | 6 · 4 |
| `INT-MOD` | LIA (`QF_LIA`) | ✓ inl. [2] | 1 Int (unbounded) | none | `x_u mod K ≠ x_v mod K` | m (n `mod` terms) | 5 · 5 |
| `INT-POW2` | NIA + `int.pow2` (`ALL`) | ✓ inl. | 1 Int exponent e | `0 ≤ e ≤ K−1`, color `2^e` | `2^e_u ≠ 2^e_v` | 2n + m | 3 · 5 |

### Bit-vectors and floating point

| Encoding | Theory (logic) | k-colorer? | Variables per node | Node constraint | Edge constraint | Size | Solved cvc5 · Z3 |
|---|---|---|---|---|---|---|---|
| `BV` | BV (`QF_BV`) | ✓; ✓ P2 for K = 2^w (Example 5) | 1 vector, ⌊log₂K⌋+1 bits (w bits if K = 2^w) | `1 ≤u x ≤u K`; nothing if K = 2^w | `x_u ≠ x_v` | 2n + m (m if K = 2^w) | 6 · 6 |
| `BV-ZERO` | BV (`QF_BV`) | ✓; ✓ P2 for K = 2^w | 1 vector, w bits | `x ≤u K−1`; nothing if K = 2^w | `x_u ≠ x_v` | n + m | 6 · 6 |
| `BV-AND` | BV (`QF_BV`) | ✓ | 1 vector, w bits | one `(x & M) ≠ 0` per 1-bit of 2^w − K (≤ w−1) | `x_u ≠ x_v` | ≤ (w−1)n + m | 6 · 6 |
| `BV-MOD` | BV (`QF_BV`) | ✓ inl. [2] | 1 vector, 32 bits | none | `x_u urem K ≠ x_v urem K` | m (n 32-bit dividers) | 5 · 5 |
| `BV-ONEHOT` | BV (`QF_BV`) | ◐ | 1 vector, K bits | `x ≠ 0`, `x & (x−1) = 0` | `(x_u & x_v) = 0` | 2n + m | 6 · 6 |
| `BV-ORDER` | BV (`QF_BV`) | ✓ | 1 vector, K−1 bits | `x & (x+1) = 0` | `x_u ≠ x_v` | n + m | 6 · 6 |
| `BV-ORDER-SHIFT` | BV (`QF_BV`) | ✓ | 1 vector, K−1 bits | `(x >> 1) & ~x = 0` | `x_u ≠ x_v` | n + m | 6 · 6 |
| `FP` | FP (`QF_FP`) | ◐ [3] | 1 Float32 | `1.0 ≤ x ≤ 1 + (K−1)·2⁻²³` (`fp.leq`) | `¬fp.eq(x_u, x_v)` | 2n + m | 5 · 6 |

### Real arithmetic

| Encoding | Theory (logic) | k-colorer? | Variables per node | Node constraint | Edge constraint | Size | Solved cvc5 · Z3 |
|---|---|---|---|---|---|---|---|
| `NLRA` | NRA (`QF_NRA`) | ✓ (Example 4's form) | 1 Real | `(x−1)(x−2)…(x−K) = 0` (degree K) | `x_u ≠ x_v` | n + m, terms O(nK) | 0 · 5 |
| `NLRA-SQRT` | NRA (`QF_NRA`) | ✓ | 1 Real | `x > 0`, `(x²−1)…(x²−K) = 0` (degree 2K) | `x_u ≠ x_v` | 2n + m, terms O(nK) | 0 · 5 |
| `NLRA-ROOTS` | NRA (`QF_NRA`) | ✗ [4] | 2 Reals (a, b) | `a²+b² = 1`, `Re((a+bi)^K) = 1`, `Im(…) = 0` | `a_u ≠ a_v ∨ b_u ≠ b_v` | 3n + m, terms O(nK) | 0 · 5 |
| `NLRA-SIN` | NRA + trig (`QF_NRAT`) | ✓ | 1 Real | 2 bounds, `sin x = 0` | `x_u ≠ x_v` | 3n + m | 1 · – |
| `NLRA-COS` | NRA + trig (`QF_NRAT`) | ✓ | 1 Real | 2 bounds, `cos x = 0` | `x_u ≠ x_v` | 3n + m | 2 · – |
| `NLRA-SINCOS` | NRA + trig (`QF_NRAT`) | ✓ | 1 Real | 2 bounds, `sin x · cos x = 0` | `x_u ≠ x_v` | 3n + m | 2 · – |
| `NLRA-SINPI` | NRA + trig (`QF_NRAT`) | ✓ | 1 Real | 2 bounds, `sin(πx) = 0` | `x_u ≠ x_v` | 3n + m | 0 · – |

The trig encodings never return SAT in cvc5 (their colors are transcendental); dReal finds the SAT models (see the README).

### Finite fields

| Encoding | Theory (logic) | k-colorer? | Variables per node | Node constraint | Edge constraint | Size | Solved cvc5 · Z3 |
|---|---|---|---|---|---|---|---|
| `FF-PRIME` | FF (`QF_FF`), prime K only | ✓ P2 | 1 element of GF(K) | none | `x_u ≠ x_v` | m | 0 of 3 · – |
| `FF-POLY` | FF (`QF_FF`) | ✓ | 1 element of GF(p), p ≥ K prime | `x(x−1)…(x−K+1) = 0` (degree K) | `x_u ≠ x_v` | n + m, terms O(nK) | 0 · – |
| `FF-ROOTS` | FF (`QF_FF`) | ✓ | 1 element of GF(p), K divides p−1 | `x^K = 1` (O(log K) multiplications) | `x_u ≠ x_v` | n + m | 0 · – |
| `FF-NULL` | FF (`QF_FF`) | ◐ | as `FF-ROOTS` | `x^K = 1` | `u^(K−1) + u^(K−2)v + … + v^(K−1) = 0` | n + m, edge terms O(mK) | 0 · – |

### Equality, uninterpreted functions, datatypes, propositional logic

| Encoding | Theory (logic) | k-colorer? | Variables per node | Node constraint | Edge constraint | Size | Solved cvc5 · Z3 |
|---|---|---|---|---|---|---|---|
| `UF` | EUF (`QF_UF`) | ✗ [5] | 1 constant of sort `Color` | `x = C1 ∨ … ∨ x = CK` | `x_u ≠ x_v` | K(K−1)/2 + n disjunctions of K + m | 6 · 6 |
| `LIST-UF` | EUF (`QF_UF`) | ✗ [5] | 1 constant of sort `List` | `x = t_1 ∨ … ∨ x = t_K`, t_j nested `cons` terms | `x_u ≠ x_v` | K(K−1)/2 + nK + m, terms O(K) | 6 · 6 |
| `UF-CARD` | EUF + cardinality (`QF_UFC`) | cvc5 ✓ P2 [6]; Z3 ✗ (quantifier) | 1 constant of sort `Color` | none; one global `|Color| ≤ K` | `x_u ≠ x_v` | 1 + m (Z3: one `∀`) | 6 · 6 |
| `LIST-DT` | datatypes (`QF_DT`) | ✗ as written; ✓ P2 without the disjunction [7] | 1 value of `Color = C1 | … | CK` | `x = C1 ∨ … ∨ x = CK` | `x_u ≠ x_v` | nK + m | 6 · 6 |
| `PEANO` | datatypes (`QF_DT`) | ✗ [8] | 1 value of `Nat = Z | S(Nat)` | `¬(is-S(x) ∧ … ∧ is-S(pred^(K−1) x))`, a clause | `x_u ≠ x_v` | n clauses of K + m | 6 · 5 |
| `BOOL-DIRECT` | propositional (`QF_SAT`; Z3 `QF_FD`) | ✗ [9] | K Booleans | `c_1 ∨ … ∨ c_K` | `¬c_u,j ∨ ¬c_v,j` for each color j | n + mK clauses, nK variables | 6 · 6 |
| `BOOL-DIRECT-AMO` | propositional | ✗ [9] | K Booleans | as above + `¬c_a ∨ ¬c_b` for a < b | as above | n(1 + K(K−1)/2) + mK | 6 · 6 |

### Strings

| Encoding | Theory (logic) | k-colorer? | Variables per node | Node constraint | Edge constraint | Size | Solved cvc5 · Z3 |
|---|---|---|---|---|---|---|---|
| `STRING` | strings (`QF_S`) | ✗ (disjunction) | 1 String | `x = "A" ∨ … ∨ x = lit_K` | `x_u ≠ x_v` | K(K−1)/2 + nK + m | 5 · 6 |
| `STR-LEX` | strings + length (`QF_SLIA`), K ≤ 50 | ✓ | 1 String | `len x = 1`, `"A" ≤lex x ≤lex chr('A'+K−1)` | `x_u ≠ x_v` | 3n + m | 3 · 0 |
| `STR-INT` | strings + LIA (`QF_SLIA`) | ✓ | 1 String | `1 ≤ str.to_int x ≤ K`, `x = str.from_int(str.to_int x)` | `x_u ≠ x_v` | 3n + m | 3 · 2 |
| `STR-REG` | strings + regex (`QF_S`) | ✓ | 1 String | `x ∈ ("A" | … | lit_K)`, one literal | `x_u ≠ x_v` | n + m (one shared regex of K) | 5 · 4 |
| `STR-SUB` | strings (`QF_S`) | ✓ | 1 String | `str.contains(W, x)`, W with exactly K substrings | `x_u ≠ x_v` | n + m | 3 · 2 |

### Arrays

| Encoding | Theory (logic) | k-colorer? | Variables per node | Node constraint | Edge constraint | Size | Solved cvc5 · Z3 |
|---|---|---|---|---|---|---|---|
| `ARR-MAP` | arrays + LIA (`QF_ALIA`) | ✗ [10] | 1 Int index, + 1 array shared by all | `1 ≤ idx ≤ K`, color `A[idx]`; globally `A[c] = c` | `A[idx_u] ≠ A[idx_v]` | K + 2n + m | 3 · 5 |
| `ARR-EXP-<ELEM>` | arrays (`QF_A…`) | ✓ (the paper's Example 9) | 1 index i₁, K+1 arrays | `A_{j+1} = A_j[i_j ↦ e_j]` for j = 1..K, color `A_{K+1}[i₁]` | `≠` on the colors | nK + m | 5 · 6 |
| `ARR-INL-<ELEM>` | arrays (`QF_A…`) | ✓ inl. (Example 9 with the arrays inlined) | 1 index, 1 array | none; color `A[i₁ ↦ e₁]…[e_K ↦ e_K][i₁]` | `≠` on the colors | m, terms O(nK) | 5 · 6 |

### Sets, bags and relations

| Encoding | Theory (logic) | k-colorer? | Variables per node | Node constraint | Edge constraint | Size | Solved cvc5 · Z3 |
|---|---|---|---|---|---|---|---|
| `SET-CUBE-<ELEM>` | sets (`QF_…FS`) | ✓ (Example 8, plus exclusions) | 1 set | `x ⊆ {e₁..e_L}`, `x ≠ S` for the 2^L − K extra subsets | `x_u ≠ x_v` | n(1 + 2^L − K) + m | 2 · 2 |
| `SET-MASK-<ELEM>` | sets (`QF_…FS`) | ✓ | 1 set | `x ⊆ {e₁..e_L}`, `¬(x ⊆ A_b)` per 1-bit of 2^L − K | `x_u ≠ x_v` | ≤ nL + m | 2 · 1 |
| `SET-MEM-<ELEM>` | sets (`QF_…FS`) | ✓ | 1 element | `x ∈ {e₁..e_K}`, one literal | `x_u ≠ x_v` | n + m (one shared set of K) | 6 · 6 |
| `SET-CLASSES-<ELEM>` | sets (`QF_…FS`) | ✗ [11] | none (K set variables S_c in total) | none; globally `S₁ ∪ … ∪ S_K = all nodes`, `S_a ∩ S_b = ∅` | `¬(u ∈ S_c ∧ v ∈ S_c)` for each c | 1 + K(K−1)/2 + mK | 6 · 6 |
| `REL-JOIN-<ELEM>` | sets + relations (`ALL`) | ✗ [11] | none (one relation C in total) | none; globally `C ⊆ Nodes × Colors`, `C ⋈ Colors = Nodes` | none; one global `(E ⋈ C) ∩ C = ∅` | 3 constraints over relations of size n + K + m | 2 · 3 |
| `BAG-SUB-<ELEM>` | bags (`ALL`) | ✓ | 1 bag | `x ⊑ {e₁:p₁−1, …, e_L:p_L−1}` (K = p₁·…·p_L), one literal | `x_u ≠ x_v` | n + m | 0 · – |
| `BAG-UNARY-<ELEM>` | bags (`ALL`) | ✓ | 1 bag | `x ⊑ {e₁:K−1}`, one literal | `x_u ≠ x_v` | n + m | 1 · – |
| `BAG-CARD-<ELEM>` | bags + LIA (`ALL`) | ✗ [12] | 1 free value | none; globally `|setof(⊎_v {x_v:1})| ≤ K` | `x_u ≠ x_v` | 1 + m, the global term O(n) | 0 · – (`DT`: 3) |
| `BAG-NEIGHBORS-<ELEM>` | bags + LIA (`ALL`) | ✗ [13] | 1 element | `x = e₁ ∨ … ∨ x = e_K`, and `count(x_v, ⊎_{u∼v} {x_u:1}) = 0` | none per edge (inside the node constraint) | n disjunctions of K + n counts, total O(nK + m) | 1 · – |

### Disjunction and separation logic

| Encoding | Theory (logic) | k-colorer? | Variables per node | Node constraint | Edge constraint | Size | Solved cvc5 · Z3 |
|---|---|---|---|---|---|---|---|
| `OR-<ELEM>` | any (`QF_<ELEM>`) | ✗ (disjunction) | 1 element | `x = e₁ ∨ … ∨ x = e_K` | `x_u ≠ x_v` | nK + m | 6 · 6 |
| `SEP-<ELEM>` | separation logic (`ALL`) | ◐ [14] | 1 location | `(x ↦ e₁) ∗ true`; globally `c₁ ↦ e₁ ∗ … ∗ c_K ↦ e₁` | `(u ↦ e₁) ∗ (v ↦ e₁) ∗ true` | 1 + n + m | 2 · – |

## Notes

1. **`IDL`.** The literals mention a variable `zero` shared by all nodes, which Definition 2 does not allow outside the color variables. But `zero` only fixes where the colors are: naming `c_j = zero + j` (difference literals `c_j − zero = j`) turns the node part into `c_1 ≤ x ≤ c_K` over the colors, so it is a colorer up to renaming.
2. **`INT-MOD`, `BV-MOD`.** The node variable `x` is unbounded (or 32 bits), but its color is the term `x mod K`. With `v_i := x_i mod K`, `x_i` an auxiliary variable, the node part is the single literal `v_i = x_i mod K`, which implies `0 ≤ v_i < K`, and the edges are `v_u ≠ v_v`: the paper's form exactly.
3. **`FP`.** The node part is a cube that leaves exactly K floats (the paper's Example 6 shows floating point is colorable), but the edges use IEEE equality `fp.eq`, not `=`. On the K chosen floats (no NaN, no ±0) the two agree, but `¬fp.eq` is not the theory's disequality in general (NaN ≠ NaN), so this is ◐.
4. **`NLRA-ROOTS`.** A node is two variables (a point), and two points differ when `a_u ≠ a_v ∨ b_u ≠ b_v`, a disjunction, so the edges are not literals. A single complex-number vertex variable would be needed.
5. **`UF`, `LIST-UF`.** Plain EUF (`cons` is an uninterpreted function here, not the list theory) is **convex**, and by Property 1 a k-colorable theory is non-convex. So EUF has no k-colorer at all, and the disjunction in these encodings cannot be avoided. (The paper's Example 7 builds a colorer for the theory of lists, with the `car`/`cdr` axioms, which is non-convex; `LIST-UF` does not use them.)
6. **`UF-CARD` (cvc5).** The cardinality literal `|Color| ≤ K` limits the sort to K elements, so `AllDifferent_K(c) ∧ |Color| ≤ K` is a colorer in the sense of Proposition 2 (the literal mentions no vertex, so every vertex can share it). The encoding leaves out the color variables, since they only name the colors. Z3 has no cardinality literal, and its version states the limit with `∀x. x = d₁ ∨ … ∨ x = d_K`, which is not quantifier-free.
7. **`LIST-DT`.** An enumeration datatype with K constructors has exactly K values, so by Proposition 2 the sort alone is a colorer, and the disjunction `x = C1 ∨ … ∨ x = CK` is redundant (it is a consequence, not a restriction). Without it, the encoding would be ✓ P2.
8. **`PEANO`.** The node constraint `¬(is-S(x) ∧ is-S(pred x) ∧ …)` is a clause (a disjunction of negated testers), not a conjunction of literals.
9. **`BOOL-DIRECT`.** There is no single vertex variable (K Booleans per node), the domain is a clause, and each edge is K clauses. Booleans have only 2 values, so a k-colorer for k ≥ 3 cannot exist in propositional logic anyway (Property 1(a)).
10. **`ARR-MAP`.** One array `A` with `A[c] = c` is shared by all nodes, and auxiliary variables must belong to one vertex. With a copy of the array per vertex it would be a colorer (it is `LIA`'s colorer behind an array read).
11. **`SET-CLASSES`, `REL-JOIN`.** These have no vertex variable at all: a node's color is which class (or which tuple of C) contains it, and the constraints are global. They are a different reduction, not instances of Lemma 2.
12. **`BAG-CARD`.** The cardinality constraint mentions every node, so it cannot be split into one cube per vertex. Unlike `UF-CARD`, where the limit is on the sort and mentions no vertex, it is about the term `⊎_v {x_v:1}`.
13. **`BAG-NEIGHBORS`.** The domain is a disjunction (as in `OR`), and "neighbours differ" is one constraint per node over its whole neighbourhood rather than one disequality per edge.
14. **`SEP`.** The node part, `(x ↦ e₁) ∗ true` together with the global K-cell heap, does allow exactly the K cells (the heap literal mentions no vertex and can be shared like `UF-CARD`'s). The edges are separating conjunctions, `(u ↦ e₁) ∗ (v ↦ e₁) ∗ true`, instead of `u ≠ v`; they mean the same on the K cells.

**Theory-independent encodings.** For `OR`, `SET-*`, `REL-JOIN`, `BAG-*`, `ARR-EXP`, `ARR-INL` and `SEP`, the verdict does not depend on the element theory. The `UF` element theory adds `distinct(E₀, …)`, which is exactly the `AllDifferent_k(c)` of the definition, so it changes nothing. `BOOL` fails whenever more than 2 elements are needed.

## Summary

| | Encodings |
|---|---|
| ✓ k-colorer as written | `LIA`, `IDL`, `BV`, `BV-ZERO`, `BV-AND`, `BV-ORDER`, `BV-ORDER-SHIFT`, `NLRA`, `NLRA-SQRT`, the four trig encodings, `FF-POLY`, `FF-ROOTS`, `STR-LEX`, `STR-INT`, `STR-REG`, `STR-SUB`, `ARR-EXP`, `SET-CUBE`, `SET-MASK`, `SET-MEM`, `BAG-SUB`, `BAG-UNARY` (25) |
| ✓ after naming a term (inl.) | `INT-MOD`, `INT-POW2`, `BV-MOD`, `ARR-INL` (4) |
| ✓ by Proposition 2 | `FF-PRIME`, `UF-CARD` (cvc5), and `BV` / `BV-ZERO` when K is a power of 2 (2 more) |
| ◐ colorer domain, other edges | `BV-ONEHOT`, `FP`, `FF-NULL`, `SEP` (4) |
| ✗ | `NLRA-ROOTS`, `UF`, `LIST-UF`, `LIST-DT`, `PEANO`, `BOOL-DIRECT`, `BOOL-DIRECT-AMO`, `STRING`, `ARR-MAP`, `SET-CLASSES`, `REL-JOIN`, `BAG-CARD`, `BAG-NEIGHBORS`, `OR` (14) |

What the table shows:

- **Being a colorer says nothing about speed.** Among the fastest encodings are colorers (`BV`, `BV-AND`, `SET-MEM`, all 6 of 6 with both solvers) and non-colorers alike (`BOOL-DIRECT`, `UF`, `OR`, `SET-CLASSES`, also 6 of 6). The paper's point is theoretical: a colorer shows that *conjunctions of literals* in the theory are already NP-hard, which is about the theory solver, not about which encoding a full SMT solver handles best. Non-colorers simply move the case split from the theory solver into the SAT solver (as disjunctions), which SAT solvers are very good at.
- **Some theories cannot have a colorer.** EUF is convex (Property 1), so `UF` and `LIST-UF` need their disjunction, and propositional logic has only 2 values. The fact that cvc5 solves them quickly matches this: their hard part is ordinary Boolean search.
- **A colorer can hide in a single literal.** `NLRA` (one polynomial), `STR-REG` (one regex membership), `STR-SUB` (one `contains`), `SET-MEM`, `BAG-SUB` and `BAG-UNARY` (one membership or sub-bag literal) restrict a node to K values with one literal, while `SET-CUBE`, `BV-AND` and `SET-MASK` need several. Where the size grows with K differs a lot: per node O(1) literals for most, O(K) term size for the polynomial and array encodings, O(K²) clauses for `BOOL-DIRECT-AMO`, and O(K²) global literals for `UF`, `LIST-UF`, `STRING` and `SET-CLASSES`.
- **The edges are where most of the formula is.** The edge part is one constraint per edge (m in total) for all but five encodings: `BOOL-DIRECT`, `BOOL-DIRECT-AMO` and `SET-CLASSES` use K clauses per edge, `BAG-NEIGHBORS` one constraint per node, and `REL-JOIN` one constraint in total. `FF-NULL` keeps one per edge, but each is a polynomial of K terms.
