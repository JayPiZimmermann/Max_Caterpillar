# Shared subset DP for full permutation sums of tree kernels

24 October 2026. This is an exact algorithmic replacement for factorial
permutation enumeration. It supplies modular evaluations, not a separator or
a new lower-bound theorem by itself.

For a rooted oriented tree, write its generic Fourier term as
`(−a)^(N−4) ∏_edges 1/[q(q+εa)]`, where `a` is the apex frequency, `q` is the
frequency sum in the component away from the root, and `ε=+1` when the edge's
positive endpoint lies in that component. The common Fourier factor is omitted.

Fix the apex frequency and let `S` be a subset of the other frequency slots.
For a rooted signed subtree type `t`, let `F_t(S)` sum its internal kernel
over every bijection from its vertices to `S`. A leaf has value one on every
singleton. If the children are `(ε_j,t_j)`, then

\[
F_t(S)=\sum_{i\in S}
\sum_{S\setminus\{i\}=U_1\sqcup\cdots\sqcup U_k\atop |U_j|=|t_j|}
\prod_j\frac{F_{t_j}(U_j)}{q_{U_j}(q_{U_j}+\varepsilon_j a)}.
\]

The partitions are ordered. Identical children are not divided by a factorial;
their ordered assignments are distinct bijections to the original vertices.
This preserves the full `S_N` sum, including its automorphism multiplicities.
Summing over the possible apex slots, with the appropriate `(−a)^(N−4)`
factor, gives exactly the original full permutation-sum column.

The compiler canonicalizes signed rooted subtree types and caches both
subtree and forest-prefix subset states across every representative. The
result is a shared acyclic sum/product graph independent of the frequencies.
The C++ evaluator processes this graph for each apex, using one batch inverse
for all edge factors. It is single-threaded and uses prime 1000003.

The complete nine-label matching-deficient inventory has 3,822 columns. Its
compiled graph has 5,733 signed subtree types, 127,848 states, 1,081,248 terms,
and 508 distinct edge-factor slots; the binary graph is 13.5 MB. The measured
C++ time is approximately 0.063 seconds per complete row, estimating about
four minutes for 3,854 rows. The reported child RSS includes the compiler
process and was below 150 MiB.

Controls in `overnight_lower_dp_controls.json` and
`overnight_lower_dp_benchmark.json` cover:

- 24 five-input exact Fraction comparisons with direct permutation sums.
- All 258 columns at five seven-input points, matching both the stored
  modular rows and the independently certified integer rows after scaling.
- All 3,822 nine-input Python/C++ values at a benchmark point.
- Three nine-input columns independently summed over all 362,880 permutations,
  using normalized heads and positive-endpoint cuts instead of rooted subtree
  states. All match.

Reproduction:

```sh
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_lower_dp.py controls
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_lower_dp.py compile9
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_lower_dp_benchmark.py
```

The benchmark compiles `overnight_lower_dp_engine.cpp` into
`/tmp/overnight_lower_dp_engine`. Its interface is:

```sh
/tmp/overnight_lower_dp_engine DAG_FILE POINTS_TEXT OUTPUT_U32
```

The first input-text line is `number_of_rows arity`; subsequent lines contain
integer frequency tuples of exact sum zero. The output consists of native
little-endian uint32 rows, one column per supplied representative followed
by the maximum target `(-1)^(N−1)/prod(ω_i)`. The DAG binary is little endian.
Use small integer points, as in the controls, so all input subset sums fit in
signed 64-bit integers. Singular edge or target factors cause an explicit
failure. The output is flushed every sixteen rows and at completion.

No claim of a uniform matching separator follows from these performance
results. Exact separator recovery still requires an independently checked
rational or integer evaluation certificate and complete family coverage.
