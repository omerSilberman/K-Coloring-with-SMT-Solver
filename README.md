# K-Coloring with SMT Solvers

A C++ benchmark suite for **graph K-coloring encoded in different SMT theories**, solved with [cvc5](https://cvc5.github.io/). Given a graph in DIMACS `.col` format and a number of colors `K`, each encoding asks: *can the nodes be colored with at most K colors so that no edge joins two nodes of the same color?*

All encodings share the same skeleton:

1. One SMT variable `node_i` per graph node, whose **sort** depends on the theory (Int, BitVec, String, Set, Array select, datatype, ...).
2. A theory-specific **domain constraint** restricting each `node_i` to exactly K possible colors.
3. The same **edge constraint** for every edge `(u, v)`: `node_u != node_v`.

The point is to compare how the solver copes with the *same* combinatorial problem when it is expressed through different theories. Several encodings (notably the array chains) follow Roberto Sebastiani, *"Colors Make Theories Hard"* (IJCAR 2016).

---

## Repository layout

| Path | Description |
|------|-------------|
| `smt_solver_cvc5.cpp` | **Main tool.** All 17 encodings, written against the native cvc5 C++ API. Built as `smt_solver_cvc5`. |
| `smt_solver.cpp` | Older version built on [smt-switch](https://github.com/stanford-centaur/smt-switch) with a cvc5 backend; supports a subset of 8 encodings. Built as `smt_solver`. |
| `smt_solver_bv.cpp`, `smt_solver_sym.cpp` | Early standalone prototypes (smt-switch). **Not** built by CMake. |
| `benchmark.py` | Runs a set of solvers over many graphs with a timeout and prints/logs a comparison table. |
| `find_optimal_k.py` | Computes the chromatic number (or an upper bound) for each graph and writes it to `optimal_k_values.json`. |
| `gen_substring_strings.py` | Writes `substring_strings.txt`: for each K, the shortest string with exactly K distinct substrings. Run `python3 gen_substring_strings.py [MAX_K]` (default 20; 60 takes a few seconds, 80 a few minutes). |
| `substring_strings.txt` | Lookup table used by the `STR-SUB` encoding. Its absolute path is compiled into `smt_solver_cvc5`, so the binary finds it from any directory. |
| `solvers_cvc5.conf` | Solver list for `benchmark.py` that uses `build/smt_solver_cvc5`. |
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
| `IDL` | IDL | `QF_IDL` | Integer `x` with `1 <= x - zero <= K` for one shared `zero` variable (difference logic only allows `x - y <op> c`). cvc5 has no dedicated IDL engine, so this runs the LIA simplex with different pivoting settings | |
| `BV` | BV | `QF_BV` | Bit-vector of the minimal width, `1 <=u x <=u K`. When K is a power of 2 (K >= 2), width `log2 K` and no constraint (the sort has exactly K values; the smt-switch `smt_solver` version still uses the bounds) | ✓ |
| `BV-ZERO` | BV | `QF_BV` | Bit-vector of width `ceil(log2 K)` with colors `0..K-1`, so only the upper bound `x <=u K-1`. No constraint when K is a power of 2 (then identical to `BV`) | |
| `BV-AND` | BV | `QF_BV` | Bit-vector of width `w = ceil(log2 K)`; one literal `(x & M) != 0` per 1-bit of `2^w - K` (none when K is a power of 2). See [Bitwise bit-vector encodings](#bitwise-bit-vector-encodings) | |
| `BV-ONEHOT` | BV | `QF_BV` | Bit-vector of width K with exactly one bit set: `x != 0` and `(x & (x-1)) = 0`. Edges are `(u & v) = 0` instead of `u != v`. See [Bitwise bit-vector encodings](#bitwise-bit-vector-encodings) | |
| `NLRA` | NLRA | `QF_NRA` | Real `x` with `(x-1)(x-2)...(x-K) = 0` | ✓ |
| `NLRA-SIN` | NLRA + trig | `QF_NRAT` | Real `x` with `sin(x) = 0`, boxed to hold exactly K roots (K = 7: `-3pi <= x <= 3pi`). **Proves UNSAT, but never SAT for K >= 2**: cvc5 only builds rational models, and the nonzero roots are irrational | |
| `NLRA-COS` | NLRA + trig | `QF_NRAT` | Same as `NLRA-SIN` with `cos(x) = 0` and the box shifted by `pi/2`. Same SAT limitation | |
| `NLRA-SINCOS` | NLRA + trig | `QF_NRAT` | Same with `sin(x) * cos(x) = 0` (roots every `pi/2`). Same SAT limitation | |
| `NLRA-SINPI` | NLRA + trig | `QF_NRAT` | Real `x` in `[-floor((K-1)/2), ceil((K-1)/2)]` with `sin(pi * x) = 0`, so the roots are integers. Still times out on everything but trivial cases (`pi * x` is nonlinear for cvc5) | |
| `FF-PRIME` | FF | `QF_FF` | Element of `GF(K)`: the sort has exactly K values, so no domain constraint. **Prime K only.** Fast on SAT, slow on UNSAT | |
| `FF-POLY` | FF | `QF_FF` | Element of `GF(p)`, p the smallest prime `>= K`, with `x(x-1)...(x-(K-1)) = 0`. Fast on UNSAT, slow on SAT | |
| `FF-ROOTS` | FF | `QF_FF` | Element of `GF(p)`, p the smallest prime with `K \| p-1`, with `x^K = 1` (the K-th roots of unity). Fast on UNSAT, slow on SAT. See [`FF-ROOTS`](#ff-roots-k-th-roots-of-unity) | |
| `LIST-UF` | UF | `QF_UF` | Colors are `cons(nil,nil)`, `cons(cons(nil,nil),nil)`, ... over an uninterpreted `List` sort, pairwise distinct; `x` equals one of them | ✓ |
| `LIST-DT` | DT | `QF_DT` | Enumeration datatype `Color = C1 \| ... \| CK`; `x` equals one constructor | ✓ |
| `UF` | UF | `QF_UF` | Uninterpreted sort with K pairwise-distinct constants; `x` equals one of them | ✓ |
| `STRING` | STRING | `QF_S` | String `x` equal to one of K distinct literals (`"A"`, `"B"`, ...) | ✓ |
| `STR-LEX` | STRING | `QF_SLIA` | `len(x) = 1` and `"A" <= x <= chr('A'+K-1)` lexicographically. **K <= 50 only.** | ✓ |
| `STR-INT` | STRING | `QF_SLIA` | String `x` with `1 <= str.to_int(x) <= K` and `x = str.from_int(str.to_int(x))` (canonical spelling, so `"02"` cannot pose as a second `"2"`) | |
| `STR-REG` | STRING | `QF_S` | `x in ("A" \| "B" \| ...)`: membership in a union regex of K literals | |
| `STR-SUB` | STRING | `QF_S` | `str.contains(W, x)`, where `W` has exactly K distinct substrings (the empty string included), so `x` is one of them. `W` is the shortest such string, read from `substring_strings.txt`; for K beyond the table, `W` is `"a"` repeated K-1 times | |
| `SET-CUBE` | SET | `QF_FSLIA` | `x` is a subset of `{0, ..., L-1}` where `2^L >= K`; the `2^L - K` extra subsets are explicitly forbidden | |
| `SET-MEM` | SET | `QF_FSLIA` | Integer `x` with `x in {1, ..., K}` (set membership) | |
| `SET-MEM-BV` | SET | `ALL` | Bit-vector `x` with `x in {1, ..., K}` (set of bit-vectors) | |
| `SET-MEM-UF` | SET + UF | `QF_UFFS` | `x` of an uninterpreted sort with `x in {C1, ..., CK}`, plus `(distinct C1 ... CK)` since uninterpreted constants may otherwise be equal | |
| `ARR-EXP` | ARRAY | `QF_ALIA` | Sebastiani array chain with explicit array variables: `A_{j+1} = store(A_j, i_j, j)` for `j = 1..K` (`i_1` free, `i_j = j` otherwise), color `x = A_{K+1}[i_1]` | |
| `ARR-INL` | ARRAY | `QF_ALIA` | Same chain as `ARR-EXP`, but built as one nested `store(store(...))` term with no intermediate variables | |
| `ARR-MAP` | ARRAY | `QF_ALIA` | One global array with `A[c] = c` for `c = 1..K`; color `x = A[idx]` with `1 <= idx <= K`. Essentially LIA behind an array read, useful for measuring array overhead | |

The `FF-*` encodings need cvc5 built with CoCoA (see [Prerequisites](#prerequisites)).

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

- `build/smt_solver_cvc5`: native cvc5, all 17 encodings
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
| `--model` | off | Ask the solvers for models and print them all at the end. |

**How it works**

- Graphs and K values come from the JSON file. Keys are graph paths relative to the repo root. A value is either an integer K or an object `{"k": ..., "status": ...}`; entries with `"k": null` (for example `SKIPPED_TOO_LARGE`) are skipped.
- Graphs whose file does not exist are skipped without a message. If the run reports fewer graphs than expected, check that the files are on disk (see [Getting benchmark graphs](#getting-benchmark-graphs)).
- The K value does not have to be the chromatic number. Setting it one below gives an UNSAT benchmark.
- On startup the script writes `myciel3/4/5.col` into `benchmarks/` if they are missing. These come from networkx's `mycielski_graph(n)`, which is numbered differently from DIMACS: `benchmarks/myciel3.col` is a 5-cycle with chromatic number 3, while the DIMACS `benchmarks/DIMACS/myciel3.col` has 11 nodes and chromatic number 4.

**Output.** Each row shows the graph, node and edge counts, K, and then for each solver `SAT <time>`, `UNS <time>` (UNSAT), `UNK <time>` (unknown) or `TIMEOUT`. Two summary rows follow: `AVERAGE` (timeouts count as the full timeout) and `SOLVED / TOTAL` (number of SAT results). Everything printed is also written to `logs/benchmark_results_<YYYYMMDD_HHMMSS>.txt`.

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
- `bin_path`: `[binary, THEORY]`; the script appends `<graph> <K> [--model]`
- `model_prefix`: label used when printing models

Two names are handled specially: `OR-Tools` runs Google OR-Tools CP-SAT in-process, and `GC-CDCL` calls an external `gc` binary with `--bound K`.

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
