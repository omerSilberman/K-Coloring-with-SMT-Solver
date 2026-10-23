# K-Coloring with SMT Solvers

A C++ benchmark suite for **graph K-coloring encoded in different SMT theories**, solved with [cvc5](https://cvc5.github.io/). Given a graph in DIMACS `.col` format and a number of colors `K`, each encoding asks: *can the nodes be colored with at most K colors so that no edge joins two nodes of the same color?*

All encodings share the same skeleton:

1. One SMT variable `node_i` per graph node, whose **sort** depends on the theory (Int, BitVec, String, Set, Array select, datatype, ...).
2. A theory-specific **domain constraint** restricting each `node_i` to exactly K possible colors.
3. The same **edge constraint** for every edge `(u, v)`: `node_u != node_v`.

Nine encodings never look at what their elements are: they get their structure from sets, arrays, a heap or plain equality. They take the element theory as a suffix (`SET-MEM-BV`, `ARR-EXP-STR`, ...); see [Theory-independent encodings](#theory-independent-encodings-encoding-elem).

A few encodings deliberately break this skeleton to try out other ideas. Some replace `!=` with a theory-specific edge constraint (`BV-ONEHOT`, `INT-MOD`, `BV-MOD`, `FF-NULL`, `SEP`). Some have no per-node variable at all (`SET-CLASSES`, `REL-JOIN`). `UF-CARD` has no domain constraint at all: one cardinality constraint on the sort replaces all of them (see [`UF-CARD`](#uf-card-the-sorts-size-is-the-domain)). They are described in [Encodings beyond the skeleton](#encodings-beyond-the-skeleton).

The point is to compare how the solver copes with the *same* combinatorial problem when it is expressed through different theories. Several encodings (notably the array chains) follow Roberto Sebastiani, *"Colors Make Theories Hard"* (IJCAR 2016).

---

## Repository layout

| Path | Description |
|------|-------------|
| `smt_solver_cvc5.cpp` | **Main tool.** All 40 encodings, 9 of them theory-independent and runnable over any of 9 element theories, written against the native cvc5 C++ API. Built as `smt_solver_cvc5`. |
| `smt_solver.cpp` | Older version built on [smt-switch](https://github.com/stanford-centaur/smt-switch) with a cvc5 backend; supports a subset of 8 encodings. Built as `smt_solver`. |
| `smt_solver_dreal.py` | The four trig encodings (`NLRA-SIN`, `NLRA-COS`, `NLRA-SINCOS`, `NLRA-SINPI`) solved by the delta-complete solver [dReal](https://github.com/dreal/dreal4) instead of cvc5. Same command line and output as `smt_solver_cvc5`. See [dReal](#dreal-delta-complete-trig-solver). |
| `smt_solver_bv.cpp`, `smt_solver_sym.cpp` | Early standalone prototypes (smt-switch). **Not** built by CMake. |
| `gui/` | **K-Coloring Explorer**, a local web UI: pick a graph, a solver and K, see the formulas in math notation and the coloring. See [Explorer](#explorer-web-ui). |
| `benchmark.py` | Runs a set of solvers over many graphs with a timeout and prints/logs a comparison table. |
| `find_optimal_k.py` | Computes the chromatic number (or an upper bound) for each graph and writes it to `optimal_k_values.json`. |
| `gen_substring_strings.py` | Writes `substring_strings.txt`: for each K, the shortest string with exactly K distinct substrings. Run `python3 gen_substring_strings.py [MAX_K]` (default 20; 60 takes a few seconds, 80 a few minutes). |
| `substring_strings.txt` | Lookup table used by the `STR-SUB` encoding. Its absolute path is compiled into `smt_solver_cvc5`, so the binary finds it from any directory. |
| `solvers_cvc5.conf` | Solver list for `benchmark.py` that uses `build/smt_solver_cvc5`. |
| `solvers_trig.conf` | Solver list for `benchmark.py` that runs each trig encoding with both cvc5 and dReal (+ OR-Tools). |
| `solvers_switch.conf` | Solver list for `benchmark.py` that uses `build/smt_solver` (+ OR-Tools). Default config. |
| `optimal_k_values.json` | Maps graph path to the K used in benchmarks. |
| `optimal_k_values_backup_*.json` | Backup created by `find_optimal_k.py --fresh`. |
| `my_list.txt` | Example `--input-list` for `benchmark.py` (a subset of graphs to run). |
| `test.col` | Tiny triangle graph for smoke tests. |
| `benchmarks/` | Graph instances (`.col` / `.clq`). Mostly git-ignored; see [Getting benchmark graphs](#getting-benchmark-graphs). |
| `logs/` | Benchmark logs written by `benchmark.py` (git-ignored). |

---

## Encodings

The **Name** is the first argument passed to the solver binaries.

| Name | Theory | Logic | Domain encoding (for each node) | In `smt_solver`? |
|------|--------|-------|---------------------------------|:---:|
| `LIA` | LIA | `QF_LIA` | Integer `x` with `1 <= x <= K` | ✓ |
| `INT-MOD` | LIA | `QF_LIA` | Unbounded integer `x`; the color is `x mod K`, and edges are `x_u mod K != x_v mod K`. See [`INT-MOD`, `INT-POW2`](#int-mod-and-int-pow2-integers-in-disguise) | |
| `INT-POW2` | NIA (cvc5 extension) | `ALL` | `x = int.pow2(e)` with `0 <= e <= K-1`, so the colors are `1, 2, 4, ..., 2^(K-1)`. The integer counterpart of `BV-ONEHOT` | |
| `IDL` | IDL | `QF_IDL` | Integer `x` with `1 <= x - zero <= K` for one shared `zero` variable (difference logic only allows `x - y <op> c`). cvc5 has no dedicated IDL engine, so this runs the LIA simplex with different pivoting settings | |
| `BV` | BV | `QF_BV` | Bit-vector of the minimal width, `1 <=u x <=u K`. When K is a power of 2 (K >= 2), width `log2 K` and no constraint (the sort has exactly K values; the smt-switch `smt_solver` version still uses the bounds) | ✓ |
| `BV-ZERO` | BV | `QF_BV` | Bit-vector of width `ceil(log2 K)` with colors `0..K-1`, so only the upper bound `x <=u K-1`. No constraint when K is a power of 2 (then identical to `BV`) | |
| `BV-AND` | BV | `QF_BV` | Bit-vector of width `w = ceil(log2 K)`; one literal `(x & M) != 0` per 1-bit of `2^w - K` (none when K is a power of 2). See [Bitwise bit-vector encodings](#bitwise-bit-vector-encodings) | |
| `BV-MOD` | BV | `QF_BV` | Unconstrained 32-bit vector `x`; the color is `x urem K`, and edges are `x_u urem K != x_v urem K`. `INT-MOD` with bit-vectors. See [`INT-MOD`, `INT-POW2`](#int-mod-and-int-pow2-integers-in-disguise) | |
| `BV-ONEHOT` | BV | `QF_BV` | Bit-vector of width K with exactly one bit set: `x != 0` and `(x & (x-1)) = 0`. Edges are `(u & v) = 0` instead of `u != v`. See [Bitwise bit-vector encodings](#bitwise-bit-vector-encodings) | |
| `FP` | FP | `QF_FP` | Float32 `x` with `1.0 <= x <= 1 + (K-1)*2^-23`: the K consecutive floats starting at 1.0. Edges use `fp.eq`. See [`FP`](#fp-the-k-floats-after-10) | |
| `NLRA` | NLRA | `QF_NRA` | Real `x` with `(x-1)(x-2)...(x-K) = 0` | ✓ |
| `NLRA-SQRT` | NLRA | `QF_NRA` | Real `x > 0` with `(x^2-1)(x^2-2)...(x^2-K) = 0`: the colors are `sqrt(1), ..., sqrt(K)`, irrational but algebraic. See [`NLRA-SQRT`, `NLRA-ROOTS`](#nlra-sqrt-and-nlra-roots-irrational-but-algebraic) | |
| `NLRA-ROOTS` | NLRA | `QF_NRA` | Point `(a, b)` with `(a + bi)^K = 1` (expanded into two real polynomials) and `a^2 + b^2 = 1`: the corners of a regular K-gon. Edges are `a_u != a_v or b_u != b_v` | |
| `NLRA-SIN` | NLRA + trig | `QF_NRAT` | Real `x` with `sin(x) = 0`, boxed to hold exactly K roots (K = 7: `-3pi <= x <= 3pi`). **Proves UNSAT, but never SAT for K >= 2**: cvc5 only builds rational models, and the nonzero roots are irrational | |
| `NLRA-COS` | NLRA + trig | `QF_NRAT` | Same as `NLRA-SIN` with `cos(x) = 0` and the box shifted by `pi/2`. Same SAT limitation | |
| `NLRA-SINCOS` | NLRA + trig | `QF_NRAT` | Same with `sin(x) * cos(x) = 0` (roots every `pi/2`). Same SAT limitation | |
| `NLRA-SINPI` | NLRA + trig | `QF_NRAT` | Real `x` in `[-floor((K-1)/2), ceil((K-1)/2)]` with `sin(pi * x) = 0`, so the roots are integers. Still times out on everything but trivial cases (`pi * x` is nonlinear for cvc5) | |
| `FF-PRIME` | FF | `QF_FF` | Element of `GF(K)`: the sort has exactly K values, so no domain constraint. **Prime K only.** Fast on SAT, slow on UNSAT | |
| `FF-POLY` | FF | `QF_FF` | Element of `GF(p)`, p the smallest prime `>= K`, with `x(x-1)...(x-(K-1)) = 0`. Fast on UNSAT, slow on SAT | |
| `FF-ROOTS` | FF | `QF_FF` | Element of `GF(p)`, p the smallest prime with `K \| p-1`, with `x^K = 1` (the K-th roots of unity). Fast on UNSAT, slow on SAT. See [`FF-ROOTS`](#ff-roots-k-th-roots-of-unity) | |
| `FF-NULL` | FF | `QF_FF` | Same field and domain as `FF-ROOTS`, but every edge is the *equation* `u^(K-1) + u^(K-2)v + ... + v^(K-1) = 0` instead of `u != v`. See [`FF-NULL`](#ff-null-nullstellensatz-coloring) | |
| `LIST-UF` | UF | `QF_UF` | Colors are `cons(nil,nil)`, `cons(cons(nil,nil),nil)`, ... over an uninterpreted `List` sort, pairwise distinct; `x` equals one of them | ✓ |
| `LIST-DT` | DT | `QF_DT` | Enumeration datatype `Color = C1 \| ... \| CK`; `x` equals one constructor. The same as `OR-DT` | ✓ |
| `PEANO` | DT | `QF_DT` | Recursive datatype `Nat = Z \| S(pred: Nat)`; colors `Z, S(Z), ..., S^(K-1)(Z)`, enforced by one tester clause "x is not K successors deep". See [`PEANO`](#peano-unary-naturals) | |
| `UF` | UF | `QF_UF` | Uninterpreted sort with K pairwise-distinct constants; `x` equals one of them. The same as `OR-UF` | ✓ |
| `UF-CARD` | UF + cardinality | `QF_UFC` | Uninterpreted sort `Color` with **no** domain constraint per node; a single `(_ fmf.card Color K)` says the sort has at most K elements. Handled by cvc5's cardinality solver. See [`UF-CARD`](#uf-card-the-sorts-size-is-the-domain) | |
| `BOOL-DIRECT` | Propositional | `QF_SAT` | No theory: K Booleans `c_i_j` ("node i has color j") per node, the clause `c_i_1 ∨ ... ∨ c_i_K`, and `¬c_u_j ∨ ¬c_v_j` per edge and color. The textbook SAT encoding. See [`BOOL-DIRECT`](#bool-direct-the-plain-sat-encoding) | |
| `BOOL-DIRECT-AMO` | Propositional | `QF_SAT` | `BOOL-DIRECT` plus the at-most-one clauses `¬c_i_a ∨ ¬c_i_b`, so each node has exactly one color | |
| `STRING` | STRING | `QF_S` | String `x` equal to one of K distinct literals (`"A"`, `"B"`, ...). `OR-STR` up to the literals | ✓ |
| `STR-LEX` | STRING | `QF_SLIA` | `len(x) = 1` and `"A" <= x <= chr('A'+K-1)` lexicographically. **K <= 50 only.** | ✓ |
| `STR-INT` | STRING | `QF_SLIA` | String `x` with `1 <= str.to_int(x) <= K` and `x = str.from_int(str.to_int(x))` (canonical spelling, so `"02"` cannot pose as a second `"2"`) | |
| `STR-REG` | STRING | `QF_S` | `x in ("A" \| "B" \| ...)`: membership in a union regex of K literals | |
| `STR-SUB` | STRING | `QF_S` | `str.contains(W, x)`, where `W` has exactly K distinct substrings (the empty string included), so `x` is one of them. `W` is the shortest such string, read from `substring_strings.txt`; for K beyond the table, `W` is `"a"` repeated K-1 times | |
| `OR-<ELEM>` | any | `QF_<ELEM>` | `x = e_1 or ... or e_K` for K distinct elements. [theory-independent](#theory-independent-encodings-encoding-elem), default `UF` | |
| `SET-CUBE-<ELEM>` | SET + any | `QF_<ELEM>FS` | `x` is a subset of `{e_0, ..., e_(L-1)}` where `2^L >= K`; the `2^L - K` extra subsets are explicitly forbidden. [theory-independent](#theory-independent-encodings-encoding-elem), default `INT` | |
| `SET-MASK-<ELEM>` | SET + any | `QF_<ELEM>FS` | `BV-AND` with sets: `x subset {e_0, ..., e_(L-1)}`, plus one `not (x subset A_b)` per 1-bit of `2^L - K`. See [`SET-MASK`](#set-mask-bv-and-with-sets), default `INT` | |
| `SET-MEM-<ELEM>` | SET + any | `QF_<ELEM>FS` | `x in {e_1, ..., e_K}` (set membership). [theory-independent](#theory-independent-encodings-encoding-elem), default `INT`. `SET-MEM-BV` and `SET-MEM-UF` are two of its variants | |
| `SET-CLASSES-<ELEM>` | SET + any | `QF_<ELEM>FS` | No node variables: K sets `S_1..S_K` of node ids (n distinct elements) that partition all nodes, and no edge has both ends in the same `S_c`. See [`SET-CLASSES`](#set-classes-color-classes-instead-of-colors), default `INT` | |
| `REL-JOIN-<ELEM>` | SET + relations + any | `ALL` | No node variables: one relation `C` between nodes and colors, and a single constraint `(E join C) n C = {}` for all edges at once. See [`REL-JOIN`](#rel-join-the-whole-graph-in-one-formula), default `INT` | |
| `SEP-<ELEM>` | Separation logic + any | `ALL` | A heap of exactly K cells `c_1 \|-> e_1 * ... * c_K \|-> e_1`; each node points into it, and edges are `(u \|-> e_1) * (v \|-> e_1) * true` instead of `u != v`. See [`SEP`](#sep-colors-are-heap-cells), default `UF` | |
| `ARR-EXP-<ELEM>` | ARRAY + any | `QF_A<ELEM>` | Sebastiani array chain with explicit array variables: `A_{j+1} = store(A_j, i_j, e_j)` for `j = 1..K` (`i_1` free, `i_j = e_j` otherwise), color `x = A_{K+1}[i_1]`. [theory-independent](#theory-independent-encodings-encoding-elem), default `INT` | |
| `ARR-INL-<ELEM>` | ARRAY + any | `QF_A<ELEM>` | Same chain as `ARR-EXP`, but built as one nested `store(store(...))` term with no intermediate variables. Default `INT` | |
| `ARR-MAP` | ARRAY | `QF_ALIA` | One global array with `A[c] = c` for `c = 1..K`; color `x = A[idx]` with `1 <= idx <= K`. Essentially LIA behind an array read, useful for measuring array overhead | |

The `FF-*` encodings need cvc5 built with CoCoA (see [Prerequisites](#prerequisites)). The four trig encodings can also be solved with dReal, which does find SAT models; see [dReal](#dreal-delta-complete-trig-solver).

### Bitwise bit-vector encodings

`BV` restricts a node to K values with the unsigned bounds `1 <=u x <=u K`. `BV-AND` and `BV-ONEHOT` do the same job with bitwise operators instead. Both are k-colorers in the sense of Sebastiani's paper: each node gets a fixed conjunction of literals over constants, with no disjunctions.

#### `BV-AND`: excluding values with AND masks

Let `w` be the smallest width with `2^w >= K`. There are `2^w` bit-vectors of that width, so `E = 2^w - K` of them must be ruled out. When K is a power of 2, `E = 0` and no constraint is needed at all: the sort itself has exactly K values (Example 5 in the paper).

**The building block.** The literal `(x & M) != 0` says "x has a 1 in at least one position where M has a 1". The values it rules out are exactly those with a 0 in every position of M. For example, with `w = 3`, `(x & 110) != 0` rules out `000` and `001` and keeps the other 6 values. A mask with `m` ones rules out `2^(w-m)` values, so one literal handles `K = 2^w - 2^(w-m)`:

| Mask | Rules out | K |
|---|---|---|
| `111` | `000` | 7 |
| `110` | `000`, `001` | 6 |
| `100` | `000` ... `011` | 4 (but a power of 2 needs no mask at all) |

**Any K.** For a general E, the encoding rules out the smallest E values, `0, 1, ..., E-1`, and keeps `E, ..., 2^w - 1` as the K colors. The argument below shows that this set can always be ruled out with a few of these literals, and how to find them.

**Submasks.** Say `a` is a *submask* of `n` when every 1-bit of `a` is also a 1-bit of `n`. In other words, `a` is what you get from `n` by switching off some (possibly none, possibly all) of its 1-bits. For example, the submasks of `101` are `000`, `001`, `100` and `101`.

A set S of values is **closed under taking submasks** if switching off bits of a member always lands on another member: whenever `n` is in S, every submask of `n` is in S too. For example, with `w = 3`:

- `{000, 001, 010, 011}` is closed: switching off bits of any of them gives one of the four.
- `{000, 011}` is not closed: `011` has the submasks `001` and `010`, which are missing.

**Why closure matters.** A single literal `(x & M) != 0` rules out the values that have no 1-bit inside M. If `x` is ruled out, then switching off more bits of `x` keeps it free of 1-bits inside M, so the result is ruled out too. That means the set ruled out by a literal, and therefore by any conjunction of literals, is always closed under submasks. So only closed sets can be excluded this way. For instance, no combination of literals rules out `011` alone without also ruling out `000`, `001` and `010`. That is why the encoding excludes the *smallest* E values: `{0, ..., E-1}` is closed (next step), so it is a set that can be excluded.

The construction, step by step:

1. **`{0, ..., E-1}` is closed under submasks.** Switching off bits can only make a number smaller, so a submask is never larger than the number itself. If `n < E`, every submask of `n` is also `< E`, so it is in the set.
2. **A closed set is fully described by its maximal elements.** Call a member *maximal* if it is not a submask of any other member. Every member is a submask of some maximal member (keep switching bits *on* while staying inside the set; this has to stop eventually). Conversely, by closure, every submask of a maximal member is in the set. So the set is exactly the union of the submasks of its maximal members, and to rule out the whole set it is enough to rule out the submasks of each maximal member.
3. **One literal per maximal member.** `x` is a submask of `a` exactly when `x` has no 1-bit outside `a`, that is, when `x & ~a = 0`. So the literal `(x & ~a) != 0` rules out precisely the submasks of `a`. Taking one such literal per maximal member rules out exactly `{0, ..., E-1}` and nothing else.
4. **Finding the maximal members.** There is one for each 1-bit of E. For the 1-bit of E at position `b`, build `a_b` in two moves:
   - *Clear bits `b..0` of E.* This keeps E's bits above position `b` unchanged and turns bit `b` (a 1 in E) into a 0. Because the first difference from E, reading from the top, is a 0 where E has a 1, the result is smaller than E no matter what the lower bits are.
   - *Set bits `b-1..0`.* The lower bits are free, so make them all 1: that is the largest number with this prefix, and every other number with the same prefix is a submask of it.

   In code: `(E >> (b+1)) << (b+1)` clears bits `b..0`, and `| ((1 << b) - 1)` sets bits `b-1..0`, giving `a_b = ((E >> (b+1)) << (b+1)) | ((1 << b) - 1)`.

   These cover everything: take any `n < E` and look at the highest position `b` where `n` and E differ. Since `n < E`, E has a 1 there and `n` has a 0, and above `b` they agree. That is exactly the shape of `a_b`, so `n` is a submask of `a_b`.

**Worked example: K = 11.** Then `w = 4` (16 values) and `E = 16 - 11 = 5 = 0101`, so the values to rule out are `0000 ... 0100` (0 to 4). E has 1-bits at positions 2 and 0:

| `b` | Clear bits `b..0` of `0101` | Set bits `b-1..0` | `a_b` | Submasks of `a_b` (ruled out) | Literal `(x & ~a_b) != 0` |
|---|---|---|---|---|---|
| 2 | `0000` | `0011` | `0011` (3) | `0000`, `0001`, `0010`, `0011` | `(x & 1100) != 0` |
| 0 | `0100` | nothing to set | `0100` (4) | `0000`, `0100` | `(x & 1011) != 0` |

Together the two literals rule out `{0, 1, 2, 3, 4}`, exactly the E = 5 smallest values, and keep the 11 values `0101 ... 1111`. Reading the literals directly: `(x & 1100) != 0` says "x is at least 4", and `(x & 1011) != 0` says "x is not 0 or 4".

So the number of literals per node is the number of 1-bits in `2^w - K`: zero for powers of 2, one for `K = 2^w - 2^j`, and never more than `w - 1`.

| K | w | E | Literals per node | Colors |
|---|---|---|---|---|
| 5 | 3 | 3 = `011` | `(x & 101) != 0`, `(x & 110) != 0` | `011` ... `111` |
| 6 | 3 | 2 = `010` | `(x & 110) != 0` | `010` ... `111` |
| 7 | 3 | 1 = `001` | `(x & 111) != 0` | `001` ... `111` |
| 9 | 4 | 7 = `0111` | `(x & 1001) != 0`, `(x & 1010) != 0`, `(x & 1100) != 0` | `0111` ... `1111` |
| 11 | 4 | 5 = `0101` | `(x & 1011) != 0`, `(x & 1100) != 0` | `0101` ... `1111` |

The construction was checked by brute force for every K up to 1024. Compared to `BV`, the restriction is the same kind of thing (`x >=u E`), but after bit-blasting each `(x & M) != 0` is a single clause ("one of these bits is 1"), where an unsigned comparison is a small comparator circuit.

#### `BV-ONEHOT`: one bit per color

Each node is a bit-vector of width K, and color `c` is the vector with only bit `c` set. Two literals force exactly one set bit:

- `x != 0`: at least one bit is set.
- `(x & (x - 1)) = 0`: at most one bit is set. Subtracting 1 clears the lowest set bit and turns the zeros below it into ones, so `x & (x - 1)` is `x` with its lowest set bit removed. It is 0 exactly when `x` had at most one set bit.

Since two one-hot vectors are equal exactly when they share their single bit, the edge constraint becomes bitwise too: `(u & v) = 0` instead of `u != v`. To support this, `AbstractGraphColorer` has a virtual `edge_constraint(u, v)` that defaults to `u != v`.

This is the opposite trade-off to `BV-AND`: width K instead of `ceil(log2 K)`, but every color is a single bit, so after bit-blasting the solver works with K Boolean "node has color c" variables, close to the classic SAT encoding of graph coloring. It is not purely bitwise, since `x - 1` is a subtraction.

### `FF-ROOTS`: K-th roots of unity

A finite field `GF(p)`, for a prime p, is the integers `0, ..., p-1` with addition and multiplication mod p. `FF-PRIME` uses it directly when K is prime, but in general p and K differ, so the node has to be restricted to K of the p elements. `FF-POLY` does this by listing the allowed values as the roots of a product. `FF-ROOTS` uses a single equation instead:

```
x^K = 1
```

**Why it has exactly K solutions.** In `GF(p)` the nonzero elements form a *cyclic* group under multiplication: there is a generator `g` whose powers `g^0, g^1, ..., g^(p-2)` run through all `p - 1` nonzero elements. Write `x = g^i`. Then `x^K = g^(iK)`, which is 1 exactly when `iK` is a multiple of `p - 1`. If K divides `p - 1`, this happens exactly when `i` is a multiple of `(p-1)/K`, which gives K values of `i` in `0, ..., p-2`. So `x^K = 1` has exactly K solutions, the *K-th roots of unity*, and they are the K colors. (`x = 0` is never a solution, since `0^K = 0`.)

**Choosing p.** The code needs a prime p with `K | p-1`, i.e. `p = 1 (mod K)`. It tries `K+1, 2K+1, 3K+1, ...` and stops at the first prime; Dirichlet's theorem guarantees one exists. If K did not divide `p - 1`, `x^K = 1` would have fewer than K solutions (`gcd(K, p-1)` of them), so this condition is what makes the count exact.

**Examples.**

| K | p | Colors (solutions of `x^K = 1` mod p) |
|---|---|---|
| 3 | 7 | `{1, 2, 4}`: `2^3 = 8 = 1`, `4^3 = 64 = 1 (mod 7)`. These are the powers of 2 mod 7 |
| 4 | 5 | `{1, 2, 3, 4}`: every nonzero element (Fermat's little theorem: `x^(p-1) = 1`) |
| 5 | 11 | `{1, 3, 4, 5, 9}`: e.g. `3^5 = 243 = 22*11 + 1` |
| 6 | 7 | `{1, 2, 3, 4, 5, 6}`: again all nonzero elements |

**How the term is built.** `x^K` is built by repeated squaring (`x^2`, `x^4`, `x^8`, ... multiplied together according to the binary digits of K), so it takes about `2 log2 K` multiplications rather than K. For example `x^5 = x * (x^2)^2`. Compared to `FF-POLY`, both domain constraints are polynomials of degree K, but `x^K - 1` has only two terms, while the product `x(x-1)...(x-(K-1))` expands to up to K+1 terms. The trade-off is a larger field: p is the first prime `= 1 (mod K)`, which can be well above the smallest prime `>= K` that `FF-POLY` uses (e.g. K = 5 needs p = 11 here, but p = 5 for `FF-POLY`).

The edge constraint is the usual `u != v`.

### `UF-CARD`: the sort's size is the domain

Every other encoding restricts each node to K colors with its own domain constraint. In `UF-CARD`, there are no colors and no domain constraints at all:

```
(declare-sort Color 0)               ; an uninterpreted sort
(declare-const node_1 Color) ...     ; one constant per node
(assert (not (= node_u node_v)))     ; one disequality per edge
(assert (_ fmf.card Color K))        ; the sort has at most K elements
```

The last line is a **cardinality constraint**, a cvc5 extension (the `C` in the logic `QF_UFC`). The nodes' values are elements of `Color`, so "at most K elements in `Color`" is "at most K distinct colors". It is the same idea as `BV` when K is a power of 2, or `FF-PRIME` when K is prime, where the sort has exactly K values, but it works for every K.

**How cvc5 solves it.** The constraint is handled by the *UF with cardinality* solver (Reynolds, Tinelli et al., built for finite model finding). It keeps the equivalence classes of `Color` terms and the disequalities between them as a graph, split into *regions* of strongly connected terms. To satisfy the constraint it must merge the classes down to at most K, never merging two classes that are disequal: that is K-coloring the disequality graph, which is our graph. It does this with two kinds of reasoning:

- **Splitting**: pick two classes in a region that are not disequal and either merge them (`node_i = node_j`: same color) or keep them apart (`node_i != node_j`: a new edge). This is **Zykov's contraction/addition branching**, the classic exact algorithm for the chromatic number: merging contracts two nodes into one, keeping them apart adds an edge.
- **Clique conflicts**: if K + 1 classes are pairwise disequal, no merge can help, and it reports a conflict right away: the clause "these K + 1 nodes cannot all be different". The cliques do not have to be in the original graph. They usually appear in the *contracted* graph after a few merges.

Two things set this apart from every other encoding. First, **there is no color symmetry**: the colors are anonymous classes, so the search never revisits the K! relabelings of one coloring, which `BV`, `LIA` and `UF` all explore. Second, a clique conflict is found in one step, while a SAT solver must rediscover "K + 1 pairwise different nodes" as a pigeonhole argument, whose resolution proofs are exponentially long.

cvc5 has other modes for this solver (`--uf-ss=no-minimal`, `none`), but they only work together with quantifier model finding and answer UNKNOWN here, so `UF-CARD` uses the default (`full`). Models print each node as an abstract element (`@Color_0`, `@Color_1`, ...).

**Complete graphs.** `K_(K+1)` with K colors is the pigeonhole problem in its purest form:

| K | `UF-CARD` | `BV` | `UF` |
|---|---|---|---|
| 8 | 0.12 s | 0.22 s | 0.51 s |
| 9 | 0.12 s | 0.62 s | 2.51 s |
| 10 | 0.12 s | 1.12 s | timeout (30 s) |
| 11 | 0.12 s | 2.81 s | timeout |
| 12 | 0.12 s | 11.03 s | timeout |

`UF-CARD` is instant for every K, since the whole graph is a (K+1)-clique. `BV` doubles with every step.

**DIMACS benchmarks.** Each graph with a proven chromatic number χ in `optimal_k_values.json` was run with K = χ (SAT) and K = χ - 1 (UNSAT), 30 s timeout, 8 runs in parallel, every SAT model checked. The run was stopped after 312 of 570 runs. The table counts the 30 SAT and 30 UNSAT instances that all five solvers completed:

| | `UF-CARD` | `BV` | `BV-AND` | `LIA` | `UF` |
|---|---|---|---|---|---|
| UNSAT solved | 19 | **24** | **24** | 13 | 19 |
| UNSAT, fastest | **10** | 2 | 5 | 1 | 7 |
| SAT solved | 18 | **29** | **29** | 20 | 26 |
| SAT, fastest | 2 | **16** | 11 | 0 | 0 |

UNSAT instances, in seconds (T/O = timeout), with χ and the clique number ω (computed with networkx):

| Graph | K | χ | ω | `UF-CARD` | `BV` | `BV-AND` | `LIA` | `UF` |
|---|---|---|---|---|---|---|---|---|
| `5-FullIns_4` | 8 | 9 | 7 | **17.56** | T/O | T/O | T/O | T/O |
| `4-FullIns_4` | 7 | 8 | 6 | **9.77** | 14.37 | 14.25 | T/O | T/O |
| `5-FullIns_3` | 7 | 8 | 7 | **0.07** | 0.77 | 0.76 | T/O | 0.47 |
| `4-FullIns_3` | 6 | 7 | 6 | **0.05** | 0.23 | 0.22 | 22.62 | 0.12 |
| `david` | 10 | 11 | 11 | **0.04** | 1.57 | 1.06 | T/O | T/O |
| `huck` | 10 | 11 | 11 | **0.08** | 1.48 | 1.27 | T/O | T/O |
| `anna` | 10 | 11 | 11 | **0.48** | 0.91 | 1.81 | T/O | T/O |
| `jean` | 9 | 10 | 10 | 12.59 | 0.61 | **0.47** | T/O | 7.30 |
| `games120` | 8 | 9 | 9 | T/O | **0.24** | **0.24** | T/O | 1.79 |
| `DSJR500.1` | 11 | 12 | 12 | T/O | 11.90 | **11.22** | T/O | T/O |
| `3-FullIns_4` | 6 | 7 | 5 | 2.04 | 2.05 | **1.81** | T/O | 3.00 |
| `1-FullIns_5` | 5 | 6 | 3 | T/O | **2.82** | 2.99 | T/O | 8.32 |
| `DSJC125.1` | 4 | 5 | 4 | 5.29 | 0.09 | 0.09 | 2.34 | **0.08** |
| `4-Insertions_3` | 3 | 4 | 2 | T/O | 2.83 | 2.79 | 6.04 | **1.28** |
| `ash958GPIA` | 3 | 4 | 3 | T/O | 1.21 | 1.16 | 3.41 | **0.63** |

`UF-CARD` wins big, often by 10-40x, on the `FullIns` graphs with ω close to χ, and on `david`, `huck` and `anna`. It is the only solver that solves `5-FullIns_4`. A clique in the original graph is *not* what makes the difference, though. On the `FullIns` graphs, ω = χ - 2 or χ - 1, so most of them have no (K+1)-clique to find. The cliques appear after a few merges, and the symmetry-free Zykov search reaches them quickly. Conversely, `jean`, `games120` and `DSJR500.1` have ω = χ, yet `UF-CARD` is slow or times out: in these larger, sparser graphs it does not find the merges that expose the clique, while the SAT solver's learned clauses do. It also fails where the gap between ω and χ is large (`1-FullIns_5`: ω = 3, χ = 6; the triangle-free `Insertions` graphs: ω = 2).

On SAT instances `UF-CARD` is slower than `BV` almost everywhere: building a model one merge decision at a time cannot compete with CaDiCaL's propagation.

So `UF-CARD` does not replace `BV`, but it complements it: it is fastest on a family of hard UNSAT instances that `BV` struggles with. A portfolio running both would beat either alone. Breaking the color symmetry in `BV` (e.g. pre-coloring a clique) might recover part of the advantage there too.

`homer.col` was left out: it contains a self-loop (`e 95 95`), so it has no coloring for any K, and every solver correctly answers UNSAT for the K = 13 stored in `optimal_k_values.json` (DSATUR ignores self-loops).

### `BOOL-DIRECT`: the plain SAT encoding

`BV` reduces to SAT by bit-blasting. `BOOL-DIRECT` skips the theory entirely and writes the SAT problem directly, in logic `QF_SAT` (no theory solver at all, just cvc5's CaDiCaL). It is the *direct encoding* from the SAT literature, one Boolean per (node, color) pair:

```
c_i_1 ∨ c_i_2 ∨ ... ∨ c_i_K        each node has a color          (n clauses)
¬c_u_j ∨ ¬c_v_j                     neighbours differ, per color   (|E| · K clauses)
¬c_i_a ∨ ¬c_i_b   for a < b         at most one color (AMO)        (n · K(K-1)/2 clauses, BOOL-DIRECT-AMO only)
```

The at-most-one clauses are optional. Without them a node may get several colors, but each of them differs from every color of every neighbour, so any one of them is a valid choice; the model printer takes the smallest. This is the same argument as for `REL-JOIN`. After bit-blasting, `BV-ONEHOT` turns into roughly this, plus the clauses for its `x & (x - 1)` arithmetic.

**Direct vs log encoding.** `BV` is the *log encoding*: ⌈log₂ K⌉ bits per node, and `u ≠ v` says "some bit differs". The two trade size against propagation:

- **Size**: the direct encoding has n·K variables and |E|·K edge clauses, the log encoding n·log₂ K bits and O(|E|·log K) clauses. With K = 73 that is 73 against 7 per node.
- **Propagation**: in the direct encoding, coloring a node immediately removes that color from all its neighbours by unit propagation (on the domains, unit propagation does what arc consistency does). In the log encoding, `u ≠ v` only propagates once all but one bit of the pair are fixed, so the solver learns much less from each decision (Walsh, "SAT v CSP", CP 2000).

**Results.** All graphs with a proven χ in `optimal_k_values.json`, at K = χ (SAT) and K = χ - 1 (UNSAT), 30 s timeout, 8 runs in parallel, every SAT model checked (`homer.col` is left out, see [`UF-CARD`](#uf-card-the-sorts-size-is-the-domain)):

| | `BV` | `BOOL-DIRECT` | `BOOL-DIRECT-AMO` |
|---|---|---|---|
| SAT solved (of 56) | 55 | **56** | 55 |
| SAT total time (timeouts as 30 s) | 140 s | **108 s** | 151 s |
| SAT, fastest | **32** | 23 | 1 |
| UNSAT solved (of 56) | **38** | 31 | 31 |
| UNSAT total time | **609 s** | 766 s | 767 s |
| UNSAT, fastest | 14 | **20** | 4 |

Selected instances, in seconds:

| Graph | K | | `BV` | `BOOL-DIRECT` | `BOOL-DIRECT-AMO` |
|---|---|---|---|---|---|
| `le450_5b` | 5 | SAT | 9.39 | **0.73** | **0.73** |
| `le450_5a` | 5 | SAT | 4.58 | **0.66** | 0.76 |
| `le450_15a` | 15 | SAT | 16.04 | **3.51** | 4.08 |
| `hamming8-4` | 16 | SAT | T/O | **7.75** | 8.56 |
| `5-FullIns_4` | 9 | SAT | 5.82 | **2.40** | 3.32 |
| `miles1000` | 42 | SAT | **2.08** | 5.75 | 8.12 |
| `mulsol.i.1` | 49 | SAT | **0.74** | 4.17 | 8.89 |
| `inithx.i.1` | 54 | SAT | **9.88** | 22.72 | T/O |
| `miles1500` | 73 | SAT | **5.20** | 17.07 | 24.04 |
| `4-Insertions_3` | 3 | UNSAT | 3.09 | 0.78 | **0.60** |
| `queen6_6` | 6 | UNSAT | 7.04 | **2.73** | 2.90 |
| `3-FullIns_4` | 6 | UNSAT | 2.38 | **1.04** | 1.16 |
| `david` | 10 | UNSAT | **1.58** | T/O | T/O |
| `huck` | 10 | UNSAT | **1.58** | T/O | T/O |
| `queen8_12` | 11 | UNSAT | **11.08** | T/O | T/O |
| `DSJR500.1` | 11 | UNSAT | **12.99** | T/O | T/O |
| `4-FullIns_4` | 7 | UNSAT | **16.32** | T/O | T/O |

**`BOOL-DIRECT` is the first encoding that beats `BV` on a broad part of the benchmark, SAT included** (`UF-CARD` only wins on a family of UNSAT instances). The split follows the size/propagation trade-off:

- **Small K, SAT**: the direct encoding wins, often by a lot: 4-13x on the `le450` graphs, and it is the only one to solve `hamming8-4`. Here the problem is small in either encoding, and the stronger propagation pays off.
- **Large K, SAT**: `BV` wins, by 2-6x from K ≈ 40 on (`miles1000`, `mulsol.i.1`, `inithx.i.1`, `miles1500`). The direct encoding grows linearly in K, the log encoding logarithmically.
- **UNSAT**: where both finish, the direct encoding is usually faster (median 1.5x), but it times out on 7 instances that `BV` solves. Most of them (`david`, `huck`, `anna`, `jean`, `DSJR500.1`) have a clique as large as χ, so with K = χ - 1 they contain a pigeonhole problem: χ pairwise adjacent nodes and only χ - 1 colors. Pigeonhole problems are notoriously hard for SAT solvers (they need exponentially long resolution proofs), and here the direct encoding, with K variables per node instead of log₂ K, suffers more from it than `BV` does.
- **AMO hurts**: the extra clauses make `BOOL-DIRECT-AMO` slower almost everywhere (median 0.71x of `BV` on SAT, against 0.91x without them). They add n·K(K-1)/2 clauses and only forbid solutions the coloring never needed to exclude.

So `BV` remains the best single encoding (most instances solved), but `BOOL-DIRECT` is better on small-K SAT and on many UNSAT instances. Together with `UF-CARD`, which solves several of the UNSAT instances `BOOL-DIRECT` fails on (`david`, `huck`, `anna`, `4-FullIns_4`) faster than `BV`, the three make a natural portfolio.

### cvc5 options for `BV`

`BV` is the fastest encoding overall, so the question is whether cvc5's own settings can make it faster. `--opt NAME=VALUE` passes any cvc5 option through. This cvc5 build has CaDiCaL as its only bit-vector SAT backend (no Kissat or CryptoMiniSat), and by default it uses CaDiCaL for the main CDCL(T) loop as well. The candidates:

| Option | What it changes |
|---|---|
| `bitblast=eager` | Translate the whole formula to CNF up front and solve it with one SAT call, instead of bit-blasting lazily inside the SMT loop (default `lazy`) |
| `bv-solver=bitblast-internal` | Bit-blast into the main SAT solver instead of a separate bit-vector SAT solver (default `bitblast`) |
| `sat-solver=minisat` | MiniSat instead of CaDiCaL for the main CDCL(T) loop |
| `simplification=none` | Skip non-clausal preprocessing (default `batch`) |
| `decision=justification` | Justification-based decisions (default `internal`) |
| `static-learning=false` | No static learning of theory lemmas from the input |

Each configuration ran on the 34 instances where default `BV` takes at least 0.4 s or times out (from graphs with a proven χ, at K = χ and K = χ - 1), 30 s timeout, 8 runs in parallel, every SAT model checked. On the remaining instances every setting finishes in under 0.4 s.

| Configuration | Solved (of 34) | Total time (timeouts as 30 s) | Median speed vs default |
|---|---|---|---|
| default | 26 | 330 s | 1.00x |
| `bitblast=eager` | 26 | 339 s | 0.85x |
| `bitblast=eager`, `simplification=none` | 26 | 339 s | 0.88x |
| `bv-solver=bitblast-internal` | 23 | 462 s | 0.73x |
| `bv-solver=bitblast-internal`, `sat-solver=minisat` | 23 | 462 s | 0.73x |
| `decision=justification` | 26 | 329 s | 0.98x |
| `static-learning=false` | 26 | 328 s | 0.99x |
| `simplification=none` | 26 | 327 s | 1.02x |

**None of the options makes `BV` meaningfully faster.** The default is already the right setup:

- **Eager bit-blasting is about 15% slower**, almost everywhere. For these formulas lazy mode already does what eager mode promises: every assertion is a top-level bit-vector atom, so the bit-vector solver gets the whole problem at the first check and solves it with one CaDiCaL call. Eager mode only adds its own pipeline on top.
- **The internal bit-blaster is the only option that changes results.** It is 1.3-1.5x faster on SAT instances with many colors: `fpsol2.i.2` and `fpsol2.i.3` (K = 30: 2.5 s vs 3.4 s), `inithx.i.1` (K = 54: 6.4 s vs 9.7 s) and `DSJR500.1` (K = 12: 0.9 s vs 1.2 s). But it is much slower almost everywhere else: 10-20x on `anna`, `huck` and `david` (UNSAT, K = 10), 34x on `ash608GPIA` (SAT), and it times out on three instances the default solves: `ash958GPIA` and `le450_15a` (SAT), and `DSJR500.1` (UNSAT, K = 11). With MiniSat as the main SAT solver it behaves the same, so the main SAT solver does not matter here.
- **Preprocessing, the decision heuristic and static learning** are all within 2% of the default, i.e. noise. The formula has no structure for them to work on: a conjunction of bit-vector atoms with no Boolean connectives above them.

No option solves any instance that the default times out on. To beat `BV`, the formula has to change, not cvc5's settings: the [`UF-CARD`](#uf-card-the-sorts-size-is-the-domain) results suggest that removing the color symmetry is where the real gains are.

### Theory-independent encodings: `<ENCODING>-<ELEM>`

Some encodings get all their structure from a "container" theory (sets, arrays, a heap, or just equality for `OR`) and only need *some* sort with enough distinct elements in it. These are written once, and the element theory is a separate parameter: `<ENCODING>-<ELEM>` on the command line, e.g. `SET-MEM-BV`, `ARR-EXP-STR`, `SET-CLASSES-DT`. The bare name (`SET-MEM`, `ARR-EXP`, ...) uses the default element theory, the one the encoding was first written with, so it gives the same formula and logic as before.

| Encoding | Elements used for | Elements needed | Default |
|---|---|---|---|
| `OR` | the K colors: `x = e_1 or ... or e_K` | K | `UF` |
| `SET-CUBE` | the bits of a color: `x subset {e_0, ..., e_(L-1)}` | L = `ceil(log2 K)` | `INT` |
| `SET-MASK` | the same, with masks; see [`SET-MASK`](#set-mask-bv-and-with-sets) | L | `INT` |
| `SET-MEM` | the K colors: `x in {e_1, ..., e_K}` | K | `INT` |
| `SET-CLASSES` | the node ids inside the color classes | n (nodes) | `INT` |
| `REL-JOIN` | the node ids and color ids inside the tuples (shared) | `max(n, K)` | `INT` |
| `ARR-EXP`, `ARR-INL` | the array indices and stored values | K | `INT` |
| `SEP` | the location and data sort of the heap | K + 1 | `UF` |

`UF`, `STRING` and `LIST-DT` are `OR` with a fixed element theory (`STRING` uses the literals `"A", "B", ...` instead of `"0", "1", ...`). They are kept as their own encodings, since they are the baselines for their theories.

**Element theories.** Everything theory-specific lives in one place: an `ElementTheory` class (in `smt_solver_cvc5.cpp`) returns a sort, n pairwise-distinct elements of it, any side constraints needed to make them distinct, and its part of the logic name.

| `<ELEM>` | Elements `e_0, ..., e_(n-1)` | Logic part |
|---|---|---|
| `INT` | Integers `0, ..., n-1` | `LIA` |
| `REAL` | Reals `0, ..., n-1` | `LRA` |
| `BV` | Bit-vectors `0, ..., n-1` of the smallest width that holds them | `BV` |
| `STR` | String literals `"0", ..., "n-1"` | `S` |
| `UF` | Constants `E0, ..., E(n-1)` of an uninterpreted sort, plus `(distinct E0 ... E(n-1))` | `UF` |
| `DT` | Constructors of the enumeration datatype `Elem = E0 \| ... \| E(n-1)` | `DT` |
| `FF` | `0, ..., n-1` in `GF(p)`, p the smallest prime `>= n` (needs cvc5 with CoCoA) | `FF` |
| `FP` | The n Float32 values after 1.0, as in `FP`. The containers compare elements with `=`, not `fp.eq`, so NaN and `+-0` play no role | `FP` |
| `BOOL` | `false`, `true`. Only 2 elements, so it fails with an error when more are needed | (none) |

**Logic.** The logic is `QF_` + the container's part (`FS` for sets, `A` for arrays, nothing for `OR`) + the element's part: `SET-MEM-BV` runs in `QF_BVFS`, `ARR-EXP-STR` in `QF_AS`, `SET-CUBE` in `QF_LIAFS` (the same logic as `QF_FSLIA`; cvc5 accepts the parts in any order). `REL-JOIN` and `SEP` stay in `ALL`, since tuples and separation logic have no logic name to compose. The choice matters: on `myciel4` with K = 5, `ARR-EXP` takes 0.1 s in `QF_ALIA` and 0.6 s in `ALL`, and `SET-CUBE` goes from 6.3 s to 2.3 s.

**Adding an element theory** means writing one `ElementTheory` subclass and adding one line to `make_element_theory`. Every theory-independent encoding can then use it. **Adding an encoding** means deriving from `ElementGenericColorer` (which provides `make_domain(n)`, `set_of` and `set_of_bits`) and adding one line to `GENERIC_ENCODINGS` and to `make_generic_colorer`.

**Results.** `myciel3` with K = 3 (UNSAT) / `myciel4` with K = 5 (SAT), in seconds, with a 20 s timeout. Four runs went in parallel, so the times are noisy.

| Encoding | `INT` | `REAL` | `BV` | `STR` | `UF` | `DT` | `FF` | `FP` |
|---|---|---|---|---|---|---|---|---|
| `OR` | 0.12 / 0.12 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.21 |
| `SET-CUBE` | 1.02 / 10.72 | 0.91 / 15.23 | 1.61 / 2.91 | 1.01 / 5.32 | 0.61 / 5.42 | 0.31 / 0.31 | timeout / timeout | 3.62 / timeout |
| `SET-MASK` | 1.12 / 14.83 | 0.81 / 5.82 | 0.71 / timeout | 1.01 / timeout | 0.61 / 5.32 | 0.31 / 0.51 | timeout / timeout | 1.71 / timeout |
| `SET-MEM` | 0.12 / 0.12 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.31 |
| `SET-CLASSES` | 0.12 / 0.22 | 0.11 / 0.11 | 0.11 / 0.21 | 0.11 / 0.21 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.21 |
| `REL-JOIN` | 0.32 / 8.22 | 0.21 / 8.12 | 0.21 / 8.02 | 0.31 / 10.13 | 0.11 / 6.22 | 0.21 / 7.82 | 0.21 / 8.02 | 0.31 / 8.52 |
| `ARR-EXP` | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.21 / 1.51 | 0.11 / 0.11 | 0.11 / 0.11 | timeout / timeout | 0.31 / 3.42 |
| `ARR-INL` | 0.11 / 0.11 | 0.11 / 0.11 | 0.11 / 0.11 | 0.21 / 0.71 | 0.11 / 0.11 | 0.11 / 0.11 | timeout / timeout | 0.31 / 3.72 |
| `SEP` | 0.21 / timeout | 0.21 / timeout | 0.21 / timeout | 0.61 / 3.52 | 0.21 / 19.74 | 0.81 / 1.61 | 0.21 / timeout | 0.31 / 15.53 |

The element theory hardly matters when the elements are only compared for equality against a short list (`OR`, `SET-MEM`, `SET-CLASSES`). It matters a lot when the container builds many terms out of them: the set encodings over subsets (`SET-CUBE`, `SET-MASK`) are fastest with `DT`, whose elements carry no structure beyond being distinct constructors, and slowest with `FF` and `FP`. `FF` makes the array chain time out even though the same elements are fine under `SET-MEM`.

**Correctness checks.** Every combination was run on the complete graphs `K_2` .. `K_5` (`K_K` SAT, `K_(K+1)` UNSAT) and on `myciel3` (K = 4 SAT, K = 3 UNSAT), and every SAT model was checked against the edge list. All answers were correct. A few `FF` combinations timed out at 15 s on the UNSAT cases, and `BOOL` stops with an error wherever more than 2 elements are needed.

#### `SET-MASK`: `BV-AND` with sets

`SET-MASK` is `BV-AND` with every bit-vector replaced by a finite set. Pick L with `2^L >= K` and L pairwise-distinct elements `e_0, ..., e_(L-1)`. A node is a set `x`, and bit j of the old bit-vector becomes "`e_j` is in `x`":

| `BV-AND` | `SET-MASK` |
|---|---|
| bit-vector of width L | `x subset U`, `U = {e_0, ..., e_(L-1)}` (the `2^L` subsets of U) |
| `(x & ~a) != 0` ("x has a 1 outside a") | `not (x subset A)`, A = the elements of the 1-bits of `a` |

So the domain is "be a subset of U", and when K is not a power of 2, the extra `E = 2^L - K` subsets are removed with sets the node must *not* be a subset of: one `A_b` for each 1-bit `b` of E, built from the same maximal element `a_b` as in [`BV-AND`](#bv-and-excluding-values-with-and-masks). For K = 11 (L = 4, E = 5 = `0101`): `a_2 = 0011` and `a_0 = 0100`, so each node gets `x subset {e_0, e_1, e_2, e_3}`, `not (x subset {e_0, e_1})` and `not (x subset {e_2})`. Compared to `SET-CUBE`, which forbids each of the E extra subsets with its own `x != S`, this needs only `popcount(E) <= L - 1` literals per node. Edges are the usual `u != v`, as set equality.

### Encodings beyond the skeleton

The encodings in this section were added to explore unusual ideas rather than to be fast: different domains, edge constraints that are not `!=`, and encodings with no per-node variable at all. Two virtual hooks in `AbstractGraphColorer` make this possible: `edge_constraint(u, v)` receives the two nodes' terms and defaults to `u != v`, and `edge_constraint_between(u, v)` receives the node *ids*, for encodings where a node's color is not one term. `edge_constraint_between` may return a null term to assert nothing for that edge.

**First results** (20 s timeout; every SAT model was checked against the edge list):

| Encoding | `myciel3`, K = 4 (SAT) | `myciel3`, K = 3 (UNSAT) | `myciel4`, K = 5 (SAT) |
|---|---|---|---|
| `INT-MOD` | 0.03 s | 0.07 s | 0.06 s |
| `INT-POW2` | 0.14 s | 0.30 s | 0.52 s |
| `FP` | 0.21 s | 0.13 s | 0.44 s |
| `NLRA-SQRT` | 3.75 s | timeout | timeout |
| `NLRA-ROOTS` | 5.40 s | timeout | timeout |
| `FF-NULL` | timeout | 0.03 s | timeout |
| `PEANO` | 0.01 s | 0.06 s | 0.02 s |
| `SET-CLASSES` | 0.02 s | 0.02 s | 0.10 s |
| `REL-JOIN` | 0.21 s | 0.14 s | 6.22 s |
| `SEP` | 0.31 s | 0.10 s | 11.81 s |

`FF-NULL` shows the same SAT/UNSAT asymmetry as `FF-POLY` and `FF-ROOTS`: Gröbner bases find the Nullstellensatz certificate quickly but are slow at producing a solution. The algebraic `NLRA-*` encodings do find SAT models, unlike the trig ones, but are slow on UNSAT.

#### `INT-MOD` and `INT-POW2`: integers in disguise

**`INT-MOD`** gives each node an *unbounded* integer `x`, with no domain constraint at all. The color is `x mod K`, and edges compare residues: `x_u mod K != x_v mod K`. The search space is infinite, but only K residues matter, so the solver has to see that `x` and `x + K` are the same color. cvc5 handles `mod` by a constant inside linear arithmetic: it introduces `q = x div K` and `r = x mod K` with `x = K*q + r` and `0 <= r < K`, so internally it rediscovers the LIA encoding, with an extra free variable `q` per node. The printed model shows the residues (`0..K-1`), since the raw `x` values may all differ.

**`BV-MOD`** is the same idea with bit-vectors: each node is an unconstrained 32-bit vector, the color is `x urem K`, and edges are `x_u urem K != x_v urem K`. A bit-vector cannot be unbounded, so 32 bits stands in for "far wider than needed": `2^32` values fold onto K colors. Unlike `INT-MOD`, there is no linear-arithmetic shortcut: `urem` by a constant is bit-blasted into a divider circuit for every node, so the solver sees a SAT problem much larger than `BV`'s. When K is a power of 2, cvc5 rewrites `urem` into taking the low bits, which is just `BV` with extra unused high bits.

**`INT-POW2`** uses cvc5's `int.pow2` extension: `x = 2^e` with `0 <= e <= K-1`, so the colors are `1, 2, 4, ..., 2^(K-1)`. This is `BV-ONEHOT` without bit-vectors: one "bit" per color, as an integer. `int.pow2` is not linear, so cvc5 handles it lazily, with refinement lemmas checked against the current model (the same way it handles integer `iand`). The edges stay `x_u != x_v` on the powers, not on the exponents, so the solver has to reason about `pow2` and cannot just compare the `e`s.

#### `FP`: the K floats after 1.0

Floats are not dense. Between 1.0 and 2.0, Float32 (8 exponent bits, 23 stored significand bits) has exactly `2^23` values, `1 + m/2^23` for `m = 0, ..., 2^23 - 1`, one *ulp* apart. So the interval

```
1.0 <= x <= 1 + (K-1) * 2^-23
```

is a continuum of reals but holds exactly K floats. These are the colors. For K = 3 they are `1.0`, `1.00000012` and `1.00000024`, printed by cvc5 as bit patterns: sign `0`, exponent `01111111` (the bias, 127, which means `2^0`), fraction `0...00`, `0...01`, `0...10`. Both bounds are built directly from those bit patterns, so no rounding is involved in writing them.

**`fp.eq` versus `=`.** IEEE equality is not SMT equality. `fp.eq` says `+0 = -0` (two different bit patterns that compare equal) and `NaN != NaN` (even a NaN compared with itself). `=` is identity of values, so `+0 != -0` and `NaN = NaN`. The edges here use `not (fp.eq u v)`. If the domain allowed NaN, every node could be NaN: `fp.eq(NaN, NaN)` is false, so every edge would hold and every graph would be 1-colorable. With signed zeros, `fp.eq` would instead merge two values into one color. The bounds rule both out: `fp.leq` is false whenever an argument is NaN, and `+-0` and the infinities lie outside `[1, 2)`. On this domain `fp.eq` and `=` agree. cvc5 bit-blasts floating point (via SymFPU), so this ends up as a bit-vector problem where the comparisons become IEEE comparison circuits.

cvc5's default FP solver only accepts Float32 and Float64. A smaller format, such as 3 exponent bits and just enough significand bits for K, needs the experimental `--fp-exp` solver.

#### `NLRA-SQRT` and `NLRA-ROOTS`: irrational but algebraic

These two encodings test *why* the trig encodings never return SAT (see [dReal](#dreal-delta-complete-trig-solver)). The trig roots are irrational, but more importantly **transcendental**: π is not the root of any polynomial with integer coefficients. cvc5's nonlinear real solver works with **real algebraic numbers**, the roots of integer polynomials, which it stores exactly as a polynomial together with an isolating interval. So it can represent √2 but not π.

**`NLRA-SQRT`**: `x > 0` and `(x^2 - 1)(x^2 - 2)...(x^2 - K) = 0`. The colors are `√1, √2, ..., √K`, mostly irrational. The answer to the question is: **SAT**. On the triangle with K = 3, cvc5 returns (polynomials written out more readably)

```
node_1: (_ real_algebraic_number <x^6 - 6x^4 + 11x^2 - 6, (11/8, 3/2)>)            = √2
node_2: 1.0
node_3: (_ real_algebraic_number <x^6 - 6x^4 + 11x^2 - 6, (3632373/2097152, 1816187/1048576)>) = √3
```

Each value is "the unique root of this polynomial in this interval": `x^6 - 6x^4 + 11x^2 - 6 = (x^2-1)(x^2-2)(x^2-3)`, the interval `(1.375, 1.5)` contains only √2, and the interval around 1.732 contains only √3. So irrationality is not the problem. Transcendence is.

**`NLRA-ROOTS`**: the trig encoding written with algebra instead of trig. The K-th roots of unity `e^(2πij/K) = cos(2πj/K) + i sin(2πj/K)` are the corners of a regular K-gon on the unit circle. Each node is a point `(a, b)`, and `(a + bi)^K = 1` is expanded by multiplying `(re + im*i)(a + bi) = (re*a - im*b) + (re*b + im*a)i` K-1 times, giving two real polynomial equations: `Re = 1` and `Im = 0`. `a^2 + b^2 = 1` follows from them, but is asserted too as a hint. The coordinates `cos(2πj/K)` are algebraic, so cvc5 can find them. For K = 3 it returns `(-1/2, ±√3/2)` and `(1, 0)`, with `√3/2` given as the root of `4x^2 - 3`. Two nodes have the same color exactly when both coordinates agree, so the edge constraint is `a_u != a_v or b_u != b_v` (written with `edge_constraint_between`, since a node is two variables).

#### `FF-NULL`: Nullstellensatz coloring

A classic idea from algebraic combinatorics (Bayer 1982; De Loera, Lee, Margulies, Onn, *"Expressing combinatorial problems by systems of polynomial equations and Hilbert's Nullstellensatz"*, 2009): write graph coloring as a system of polynomial **equations**, with no `!=` at all. The domain is the same as `FF-ROOTS` (`x^K = 1` in `GF(p)`, `p = 1 mod K`), and each edge becomes

```
u^(K-1) + u^(K-2) v + u^(K-3) v^2 + ... + v^(K-1) = 0
```

**Why this means `u != v`.** The left side is `(u^K - v^K) / (u - v)`, the geometric-series factorization of `u^K - v^K`. For two K-th roots of unity:

- If `u != v`: `u^K - v^K = 1 - 1 = 0` while `u - v != 0`, so the quotient is 0.
- If `u = v`: every term is `u^(K-1)`, so the sum is `K * u^(K-1)`. `u` is nonzero, and `K` is nonzero in `GF(p)` because `p = 1 (mod K)` means `p > K`, so p does not divide K. A product of nonzero field elements is nonzero, so the equation fails.

For K = 3, the edge polynomial is `u^2 + uv + v^2 = 0`. In `GF(7)` with colors `{1, 2, 4}`: `1 + 2 + 4 = 7 = 0` for `(u, v) = (1, 2)`, and `3 * 1 = 3 != 0` for `u = v = 1`.

The point of the theorem: the graph is **not** K-colorable exactly when 1 lies in the ideal generated by these polynomials, i.e. `1 = sum of g_i * f_i` for some polynomials `g_i`. That identity, a *Nullstellensatz certificate*, is a purely algebraic proof of non-colorability. cvc5's finite-field solver works with Gröbner bases, so an UNSAT answer here comes from deriving exactly such a certificate. Each edge polynomial has K terms, so the formula grows with `K * |E|`. It needs cvc5 built with CoCoA, like the other `FF-*` encodings.

#### `PEANO`: unary naturals

A recursive datatype `Nat = Z | S(pred: Nat)`, with the colors `Z, S(Z), S(S(Z)), ..., S^(K-1)(Z)`. `LIST-DT` lists its K constructors explicitly. Here there is only one constructor shape, and the depth is bounded with a single clause per node, built from *testers* (`is-S`) and the *selector* `pred`:

```
not (is-S(x) and is-S(pred x) and is-S(pred (pred x)) and ... and is-S(pred^(K-1) x))
```

"x is not K successors deep". In SMT-LIB, a selector applied to the wrong constructor (`pred Z`) is unconstrained and can be any value. That is harmless here: if `pred^j x` is `Z` for some `j < K`, the conjunct `is-S(pred^j x)` is already false, so the conjunction is false no matter what the later, unconstrained terms are. If `x` has depth `>= K`, all K testers are true and the clause rules it out. The datatype solver has to *build* the colors by splitting on constructors, instead of choosing from a list. (cvc5 has an internal `dt.size` function that would express "depth < K" directly, but it is not exposed through the API or the SMT-LIB parser.)

#### `SET-CLASSES`: color classes instead of colors

The usual encodings ask "which color does node i get?". This one asks "which nodes form color class c?". There are no node variables at all, just K set variables `S_1, ..., S_K` over the node ids:

- **Partition**: `S_1 u ... u S_K = {1, ..., n}` (every node gets a color) and `S_a n S_b = {}` for `a != b` (at most one color).
- **Independent sets**: for every edge `(u, v)` and every class `c`, `not (u in S_c and v in S_c)`. This is the only place edges appear, through `edge_constraint_between`.

A node's color is the class that contains it, read from the model by evaluating `i in S_c`. With an element theory other than `INT`, the node ids are n distinct elements of that theory instead of `1, ..., n`. This is the view behind set-partitioning and column-generation approaches to coloring, where each color class is an independent set. Here cvc5's set solver has to reason about membership, union and intersection over n elements and K sets.

#### `REL-JOIN`: the whole graph in one formula

cvc5 supports **relations**, sets of tuples, with relational join, product and transpose. The edge set becomes a constant binary relation `E = {(u, v) | (u, v) is an edge}`, and the coloring is a single unknown relation `C` between nodes and colors. The whole problem is three constraints, no matter how many edges there are:

```
C  subset  Nodes x Colors          Nodes = {(1), ..., (n)},  Colors = {(1), ..., (K)}
C join Colors = Nodes              every node has at least one color
(E join C) n C = {}                no node shares a color with a neighbour
```

The join of a relation of pairs with a relation of pairs matches the inner columns: `E join C = {(u, c) | (u, v) in E and (v, c) in C}`, "u has a neighbour of color c". Intersecting with `C` gives the pairs where u itself also has color c, i.e. the conflicts. Since the condition is symmetric in u and v, `E` only needs each edge once. Similarly, `C join Colors` has arity `2 + 1 - 2 = 1`: the nodes that have some color in `Colors`.

`C` is **not** required to be a function. A node may get several colors. If the constraints hold, every color of u differs from every color of each neighbour, so picking any one color per node (the model printer takes the smallest) gives a valid coloring. Adding "at most one color" (e.g. `transpose(C) join C subset identity`) would make the formula bigger without changing the answer. `edge_constraint_between` returns a null term, so no per-edge constraints are asserted at all. With an element theory other than `INT`, nodes and colors are named by `max(n, K)` distinct elements of that theory: node i is the i-th element and color c the c-th.

#### `SEP`: colors are heap cells

Separation logic is a logic for reasoning about pointers and heaps. `x |-> d` means "the heap is exactly one cell, at location x, holding d", and `P * Q` (*separating conjunction*) means "the heap splits into two **disjoint** parts, one satisfying P and one satisfying Q". cvc5 supports it with a heap whose location and data sorts are declared once. Here both are the element sort (an uninterpreted sort by default), and every cell holds the element `e_1`, written `0` below. All top-level assertions talk about the same heap:

```
c_1 |-> 0 * c_2 |-> 0 * ... * c_K |-> 0         the heap is exactly K distinct cells
(x |-> 0) * true                                 node x points to a cell of the heap
(u |-> 0) * (v |-> 0) * true                     edge: u and v point to two different cells
```

The first line uses `*` to make the K colors distinct: disjoint heap parts must have different locations. `true` matches any leftover heap, so `(x |-> 0) * true` says "x is allocated", and since the heap is exactly the K cells, x is one of them. The edge constraint is the twist: instead of `u != v`, it says the heap contains two *separate* cells, one at u and one at v, which can only happen if `u != v`. Separation does the job of disequality. cvc5's separation logic requires non-incremental mode, which this encoding sets. Models print the nodes as abstract locations (`@Elem_1`, ...).

**The location sort needs K + 1 values.** cvc5 reserves one location, `sep.nil`, that can never be allocated. With a location sort of exactly K values (e.g. `SEP-DT` with K constructors, or `SEP-BV` when K is a power of 2), a K-cell heap cannot exist and every instance comes out UNSAT. So `SEP` asks the element theory for K + 1 elements, which only serves to size the sort. The heap must also be declared before the first assertion, which is why element theories return their side constraints (such as `distinct` for `UF`) instead of asserting them.

---

## Prerequisites

**C++ side**

Both binaries need **cvc5** built with CaDiCaL and libpoly, and `smt_solver` also needs **smt-switch**. The simplest way to get both is to let smt-switch build cvc5 for you. Everything ends up inside the smt-switch checkout, and no root access is needed except for the apt packages.

> The `cvc5` / `libcvc5-dev` packages in Ubuntu's repos won't work: they are built with CryptoMiniSat and CLN instead of CaDiCaL and libpoly, and smt-switch's cvc5 backend requires the latter.

1. Build tools (Ubuntu/Debian):

   ```bash
   sudo apt install -y g++ git cmake libgmp-dev m4 pkg-config
   ```

2. smt-switch, with cvc5 built automatically. The cvc5 build takes roughly 15-30 minutes:

   ```bash
   git clone https://github.com/stanford-centaur/smt-switch.git ~/smt-switch
   cd ~/smt-switch
   ./configure.sh --cvc5 --without-tests --prefix=$HOME/smt-switch/install
   cd build && make -j"$(nproc)" && make install
   ```

   This produces cvc5 1.4.0 (static, with CaDiCaL and libpoly) in `~/smt-switch/deps/cvc5` and smt-switch in `~/smt-switch/install`.

3. *(Only for the `FF-*` encodings.)* cvc5's finite-field solver needs the CoCoA library, which smt-switch does not enable. Rebuild cvc5 in place with it (CoCoA is GPL, so cvc5 requires `ENABLE_GPL` too, which makes the resulting build GPL-licensed):

   ```bash
   cd ~/smt-switch/deps/cvc5/src/cvc5-build
   cmake -DUSE_COCOA=ON -DENABLE_GPL=ON .
   make -j"$(nproc)" && make install
   ```

   `~/smt-switch/deps/cvc5/bin/cvc5 --show-config` should then report `cocoa : yes`. Rebuild this project afterwards.

4. *(Only for `smt_solver_dreal.py`.)* dReal 4.21.06.2, unpacked from `.deb` files into `~/dreal/root` (no root access, nothing installed system-wide). dReal's last release targets Ubuntu 20.04, so its ibex dependency comes from the dReal PPA's 24.04 build and the other libraries from your distribution:

   ```bash
   mkdir -p ~/dreal/debs && cd ~/dreal/debs
   wget https://github.com/dreal/dreal4/releases/download/4.21.06.2/dreal_4.21.06.2_amd64.deb
   wget "https://ppa.launchpadcontent.net/dreal/dreal/ubuntu/pool/main/libi/libibex-dev/libibex-dev_2.7.4.20251228014325.gitfde1b111a5439eb59b7260bb84189e1a0c9cffca~24.04_amd64.deb"
   apt-get download libnlopt0 coinor-libclp1 coinor-libcoinutils3v5 liblapack3 libblas3 libgfortran5
   for f in *.deb; do dpkg-deb -x "$f" ~/dreal/root; done
   ```

   `smt_solver_dreal.py` sets `LD_LIBRARY_PATH` itself. To use another location, set `DREAL_ROOT`.

**Python side** (for the scripts)

```bash
python3 -m venv venv
source venv/bin/activate
pip install networkx ortools
```

---

## Build

```bash
cmake -S . -B build
cmake --build build -j
```

This produces:

- `build/smt_solver_cvc5`: native cvc5, all 40 encodings
- `build/smt_solver`: smt-switch, 8 encodings

CMake finds smt-switch and cvc5 through `SMT_SWITCH_DIR`, which defaults to `~/smt-switch`. If your checkout is somewhere else, pass the path:

```bash
cmake -S . -B build -DSMT_SWITCH_DIR=/path/to/smt-switch
```

No `LD_LIBRARY_PATH` is needed to run the binaries: cvc5 is linked statically, and the path to the smt-switch libraries is built into `smt_solver`.

---

## Running a single instance

### `smt_solver_cvc5`

```bash
./build/smt_solver_cvc5 <THEORY> <graph.col> <K> [--model] [--print-asserts]
```

| Option | Effect |
|--------|--------|
| `--model` | If SAT, print the coloring (`MODEL: node_1: ... node_2: ...`). Array encodings also print their index variables (`i_1_*` or `idx_*`). |
| `--print-asserts` | Dump every asserted formula, in SMT-LIB-like syntax, before solving. |
| `--opt NAME=VALUE` | Set a cvc5 option, e.g. `--opt bitblast=eager`. Repeatable; `--opt NAME` alone means `NAME=true`. Options are set before the encoding configures the solver, so options an encoding requires (such as `SEP`'s non-incremental mode) still win. See [cvc5 options for `BV`](#cvc5-options-for-bv). |
| `--help`, `-h` | Show usage and the list of theories. |

Options can appear anywhere on the command line. The program prints one of `SAT`, `UNSAT` or `UNKNOWN`.

Example on the bundled triangle graph, which needs 3 colors:

```bash
./build/smt_solver_cvc5 LIA test.col 2            # UNSAT
./build/smt_solver_cvc5 LIA test.col 3 --model    # SAT + coloring
./build/smt_solver_cvc5 ARR-INL test.col 3 --print-asserts --model
```

### `smt_solver` (smt-switch)

```bash
./build/smt_solver <THEORY> <graph.col> <K> [--model]
```

Supports `LIA`, `BV`, `NLRA`, `LIST-UF`, `LIST-DT`, `UF`, `STRING`, `STR-LEX`. Here `--model` must be the 4th argument.

### `smt_solver_dreal.py`

```bash
./smt_solver_dreal.py <THEORY> <graph.col> <K> [--model] [--print-asserts] [--precision D] [--jobs N]
```

`THEORY` is one of `NLRA-SIN`, `NLRA-COS`, `NLRA-SINCOS`, `NLRA-SINPI`. `--print-asserts` prints the SMT-LIB query sent to dReal, `--precision` sets dReal's delta (default 0.001), and `--jobs` sets dReal's number of parallel search threads (default 8). Output is `SAT`, `UNSAT` or `UNKNOWN`, as for `smt_solver_cvc5`; models print each node's root, e.g. `node_1: 2*pi`.

### Graph format

Standard DIMACS: comment lines start with `c`, a header `p edge <nodes> <edges>`, and one `e <u> <v>` line per edge with 1-based node ids.

```
c Simple triangle graph
p edge 3 3
e 1 2
e 2 3
e 1 3
```

---

## Explorer (web UI)

`gui/` holds a small web app for running one instance and looking at it. It needs nothing beyond Python 3 and a built `build/smt_solver_cvc5`:

```bash
./gui/kcolor_gui.py               # opens http://127.0.0.1:8765/ in your browser
./gui/kcolor_gui.py --no-browser  # just print the address; --port N picks another port
```

- **Graph**: every `.col` / `.clq` under `benchmarks/` (plus `test.col`), searchable, with its node and edge counts. K defaults to the value in `optimal_k_values.json`, with a link back to it if you change K.
- **cvc5 options**: clickable chips under the solver for the options worth trying, shown only where they apply (eager bit-blasting only for the pure bit-vector encodings). Each chip's tooltip says what it did to `BV` in the benchmark. Any other option can be typed as `NAME=VALUE`; a typed option overrides a chip with the same name.
- **Solver**: every theory that `smt_solver_cvc5 --help` lists, grouped by theory. The theory-independent encodings get an element-theory picker. The four trig encodings can also run with dReal (`smt_solver_dreal.py`).
- **Formulas**: the assertions from `--print-asserts`, shown as math: `node₁ ∈ {0, 1, 2}`, `A₂,₁ = A₁,₁[i₁,₁ ↦ 0]`, `(E ⋈ C) ∩ C = ∅`, `c₁ ↦ E0 ∗ c₂ ↦ E0`, with `let` bindings inlined. The **SMT-LIB** toggle shows the raw text, and the filter searches it. Up to 5,000 formulas are sent to the page; the rest are only counted.
- **While solving**: a spinner, a running timer and the phase (building the formula, solving). **Stop** kills the solver process. An optional time limit does the same automatically.
- **Result**: SAT, UNSAT, UNKNOWN, time limit or error (with the solver's message). For SAT: a legend of the colors used, with counts. The server checks the coloring against every edge ("Valid coloring", or the conflicting edges in red). Graphs up to 300 nodes are drawn with a force-directed layout, colored by the model; hovering a node shows its value, and clicking a color in the legend highlights its nodes. **Show the color of every node** lists all nodes and can be filtered. The **Node numbers / Assigned values** toggle labels the drawing and that list either by node number (and color number) or by the value the solver assigned, in a short form (`A` for `"A"`, `{E0, E1}`, `01₂`, `π` for dReal's `1*pi`).
- **Theme**: Light, Dark, or Auto (follow the system), top right. The choice is remembered.

The server (`gui/kcolor_gui.py`) only uses the standard library. It runs the solver with `--print-asserts --model` and streams its output to the page as Server-Sent Events. The page is plain HTML/CSS/JS in `gui/static/`, and `pretty.js` holds the SMT-LIB-to-math renderer. It listens on 127.0.0.1 only.

## Benchmarking

`benchmark.py` runs every enabled solver on every graph listed in the K-values JSON and prints a live comparison table.

```bash
# All graphs in optimal_k_values.json, cvc5-native solvers, 20 s timeout
python3 benchmark.py --solvers solvers_cvc5.conf

# Only the graphs in my_list.txt, 60 s timeout, also print the models
python3 benchmark.py --solvers solvers_cvc5.conf --input-list my_list.txt --timeout 60 --model
```

| Flag | Default | Description |
|------|---------|-------------|
| `--solvers FILE` | `solvers_switch.conf` | Solver configuration (see below). Pass `solvers_cvc5.conf` to use the native cvc5 binary. |
| `--json FILE` | `optimal_k_values.json` | Graphs to run and the K to test for each. |
| `--input-list FILE` | none | Text file with one graph path per line. Only JSON entries whose key matches a line are run. |
| `--timeout SECONDS` | `20.0` | Timeout per solver per graph. |
| `--k-offset N` | `0` | Test `K + N` instead of the JSON's K. `--k-offset -1` turns a run at the chromatic number into an UNSAT benchmark (graphs whose K drops below 1 are skipped). |
| `--model` | off | Ask the solvers for models and print them all at the end. |

**How it works**

- Graphs and K values come from the JSON file. Keys are graph paths relative to the repo root. A value is either an integer K or an object `{"k": ..., "status": ...}`; entries with `"k": null` (for example `SKIPPED_TOO_LARGE`) are skipped.
- Graphs whose file does not exist are skipped without a message. If the run reports fewer graphs than expected, check that the files are on disk (see [Getting benchmark graphs](#getting-benchmark-graphs)).
- The K value does not have to be the chromatic number. Setting it one below (or passing `--k-offset -1`) gives an UNSAT benchmark.
- On startup the script writes `myciel3/4/5.col` into `benchmarks/` if they are missing. These come from networkx's `mycielski_graph(n)`, which is numbered differently from DIMACS: `benchmarks/myciel3.col` is a 5-cycle with chromatic number 3, while the DIMACS `benchmarks/DIMACS/myciel3.col` has 11 nodes and chromatic number 4.

**Output.** Each row shows the graph, node and edge counts, K, and then for each solver `SAT <time>`, `UNS <time>` (UNSAT), `UNK <time>` (unknown) or `TIMEOUT`. Two summary rows follow: `AVERAGE` (timeouts count as the full timeout) and `SOLVED / TOTAL` (number of SAT or UNSAT results). Everything printed is also written to `logs/benchmark_results_<YYYYMMDD_HHMMSS>.txt`.

### Solver configuration files

A `.conf` file is a Python list literal of solver entries. Comment out a line with `#` to disable that solver:

```python
[
    {"name": "BV SMT",  "bin_path": ["./build/smt_solver_cvc5", "BV"],  "model_prefix": "C++ BV"},
    # {"name": "LIA SMT", "bin_path": ["./build/smt_solver_cvc5", "LIA"], "model_prefix": "C++ LIA"},
    {"name": "OR-Tools", "bin_path": "internal", "model_prefix": "Google"}
]
```

- `name`: column header in the results table
- `bin_path`: `[binary, THEORY]`; the script appends `<graph> <K> [--model]`. cvc5 options go in the list too: `["./build/smt_solver_cvc5", "BV", "--opt", "bv-solver=bitblast-internal"]`
- `model_prefix`: label used when printing models

Two names are handled specially: `OR-Tools` runs Google OR-Tools CP-SAT in-process, and `GC-CDCL` calls an external `gc` binary with `--bound K`.

---

## dReal: delta-complete trig solver

cvc5 proves the trig encodings UNSAT but never SAT. The roots of sin and cos (other than 0) are irrational, and cvc5 only reports SAT for a model it can check exactly. No cvc5 option changes this. A **delta-complete** solver answers a weaker question: given a small delta, it returns either `unsat` (sound, as in cvc5) or `delta-sat`, meaning each constraint holds up to delta (`f(x) = 0` becomes `|f(x)| <= delta`). dReal does this with interval constraint propagation and branch-and-prune, and reports a narrow box around each variable, e.g. `node_1 : [3.1415926535897931, 3.1415926535897936]`.

`smt_solver_dreal.py` uses the same encodings as `smt_solver_cvc5` with two differences:

- **Edges are `|u - v| >= step/2`, not `u != v`.** Under delta-weakening, `u != v` is satisfied by `u = v`, so every graph would come back delta-sat. Distinct roots are a full step apart (pi, pi/2 or 1), so a separation of half a step means "different roots". (`abs` was faster than the equivalent `or` of two inequalities.)
- **The box reaches half a step past the outermost roots**, so it still holds exactly K roots but none of them lies on its boundary. dReal has no exact pi, so pi is a decimal literal.

A `delta-sat` answer becomes an exact coloring: each node is rounded to the nearest root, and the script checks that every node lands on one of the K roots and that no edge has both ends on the same root. Only then does it print `SAT`. If the check fails, it prints `UNKNOWN`. So a `SAT` from this script is a verified K-coloring, not an approximate one.

**Performance.** dReal handles small graphs only. On `myciel3` (11 nodes) it answers both K = 4 (SAT, 0.1 s) and K = 3 (UNSAT, about 2 s). From about 20 nodes on, it mostly times out. Its parallel search (`--jobs`) is what makes `myciel4` (23 nodes, K = 5) solvable at all, but the result depends on luck: with 8 or 16 threads, repeated runs took 0.5-4 s or timed out after 15 s; with 1 or 4 threads it always timed out. Expect runtimes to vary from run to run. A larger delta did not help.

To compare it with cvc5 on both sides of the chromatic number:

```bash
python3 benchmark.py --solvers solvers_trig.conf --input-list my_list.txt              # K = chromatic number (SAT)
python3 benchmark.py --solvers solvers_trig.conf --input-list my_list.txt --k-offset -1 # K - 1 (UNSAT)
```

---

## Computing K values

`find_optimal_k.py` scans a directory recursively for `*.col` and `*.clq` files, computes a K for each, and saves the results to `optimal_k_values.json`.

```bash
python3 find_optimal_k.py                      # OR-Tools mode on ./benchmarks
python3 find_optimal_k.py OR-TOOLS benchmarks  # same, explicit
python3 find_optimal_k.py LIA benchmarks       # use ./build/smt_solver_cvc5 with the LIA encoding
python3 find_optimal_k.py BV --fresh           # back up the JSON and start over with BV
python3 find_optimal_k.py BV --timeout 300     # retry the FEASIBLE graphs with 5 minutes per call
python3 find_optimal_k.py --help               # all options
```

- **`OR-TOOLS` mode** (default) minimizes the number of colors with CP-SAT (default limit 20 s per graph).
- **Theory mode** (any theory name) starts from a known K-coloring and calls `./build/smt_solver_cvc5 <THEORY> ... --model` with K-1 until it gets UNSAT (default limit 60 s per call). When the solver's coloring uses fewer colors than it was allowed, the search jumps straight below that number instead of stepping down by one.
- **Bounds**, computed for every graph in both modes:
  - *Upper bound*: a [DSATUR](https://en.wikipedia.org/wiki/DSatur) coloring, which always colors next the node whose neighbors already use the most distinct colors. On 115 benchmark graphs it matched the best known K on 81, against 45 for the previous greedy heuristic (nodes in file order). A previous run's K is used instead if it is better.
  - *Lower bound*: a clique found greedily (grown from each of the 50 highest-degree nodes). A clique of c nodes needs c colors, so when the coloring's K equals the clique size, K is proven optimal without any solver call.
  - Both take under a second even on 200,000-edge graphs.
- `--timeout SECONDS` sets the limit per solver call (per graph for OR-Tools).
- Graphs with more than 200,000 edges are not solved and are recorded as `{"k": null, "status": "SKIPPED_TOO_LARGE"}`.

**Results.** Each graph gets an entry like `{"k": 6, "status": "OPTIMAL", "source": "SAT", "proof": "UNSAT", "clique": 5, "solver": "BV", "timeout": 60.0}`:

- `status: OPTIMAL`: K colors work and K-1 was proven impossible, so K is the chromatic number.
- `status: FEASIBLE`: K colors work (an actual coloring was found), but a solve timed out before K-1 was settled. K is an **upper bound** on the chromatic number.
- `source` says what produced the K-coloring: `DSATUR`, `SAT` (the SMT solver), `OR-TOOLS`, or `previous run`. So `FEASIBLE` from `DSATUR` means the solver never managed to improve on the DSATUR coloring.
- `proof` (only for `OPTIMAL`) says what ruled out K-1: `UNSAT`, `OR-TOOLS`, or `clique`.
- `clique` is the size of the clique found, a lower bound on K.

**Resuming.** Without `--fresh`, the file is reused and saved after every graph:

- `OPTIMAL` graphs are skipped.
- `FEASIBLE` graphs are retried starting from K-1 (their K is already known to work). Rerunning with a larger `--timeout` is how they become `OPTIMAL`.
- Graphs skipped for size are reconsidered, in case the limit was raised.
- Entries written by older versions (a bare integer K) are treated as `FEASIBLE`.

`--fresh` copies the current JSON to `optimal_k_values_backup_<unix-time>.json` and recomputes everything. `benchmark.py` reads both the old and the new format.

---

## Getting benchmark graphs

Only a few small graphs are tracked in git. Most keys in `optimal_k_values.json` point to `benchmarks/DIMACS/...`, so download the standard DIMACS graph-coloring instances (for example from the [COLOR02/03/04 collection](https://mat.tepper.cmu.edu/COLOR02/)) and put the `.col` files in `benchmarks/DIMACS/`. Then either run the benchmark directly or regenerate the K values with `find_optimal_k.py`.

---

## Reference

- R. Sebastiani. *Colors Make Theories Hard.* In Proc. International Joint Conference on Automated Reasoning (IJCAR), 2016.
