# Small-N certificates for exact expansions of the maximum

The search for expansions happens elsewhere (e.g. `research/sN/dfs/h5-growth`).
This directory turns one exact expansion into Lean source in
`MaxCaterpillar/SmallN/`. Lean then checks the claim: every cell lemma is
proved by `linarith only` and `linear_combination`, and coverage is proved by
explicit `le_total` case trees. Lean does not trust any search output.

```
python3 scripts/smalln/from_pkl.py DATA.pkl Name inputs/name.json "source note"  # optional
python3 scripts/smalln/gen_lean.py inputs/name.json [--chunk 150] [--dry]
lake build MaxCaterpillar.SmallN.Name
```

Add `import MaxCaterpillar.SmallN.Name` to `MaxCaterpillar/SmallN.lean` to
include a new instance.

## JSON input format

```json
{
 "name": "Max5Lns27",
 "N": 5,
 "source": "free text: where the data came from",
 "units": [
  {"coef": "3/2", "head": [-1, -1, 0, 1, 1], "pairs": [[0, 3], [0, 4], [2, 4]]},
  ...
 ],
 "aux": [
  {"coef": "3", "kind": "lin", "i": 0},
  {"coef": "-3/2", "kind": "pair", "i": 0, "j": 1},
  ...
 ]
}
```

The input encodes the claim, for all `x ∈ ℝ^N`:

```
max(x_0,…,x_{N-1}) = Σ_units coef · σ( Σ_i head[i]·x_i + Σ_{[i,j] ∈ pairs} σ(x_i − x_j) )
                    + Σ_aux coef · term
```

* `name`: a capitalized Lean identifier. It becomes the namespace
  `MaxCaterpillar.SmallN.<name>`, the root module
  `MaxCaterpillar/SmallN/<name>.lean`, and the folder `MaxCaterpillar/SmallN/<name>/`.
* `coef`: a rational number written as a string (`"-3/2"`, `"1"`).
* `head`: `N` rationals (JSON integers or strings such as `"1/2"`).
* `pairs`: `[i, j]` means `σ(x_i − x_j)` (`i ≠ j`, any order). `[i, j, "w"]`
  means `w·σ(x_i − x_j)` with a rational weight `w`, which may be negative.
* `aux` terms: `{"kind": "lin", "i"}` = `x_i`, `{"kind": "pair", "i", "j"}` = `σ(x_i − x_j)`.
  The kinds `pos` (`σ(x_i)`) and `neg` (`σ(−x_i)`) are also accepted. The
  identity is then still proved, but no network theorem is generated, because
  `σ(±x_i)` for `i > 0` is not a feature of the paper's first hidden layer.

A unit is therefore an arbitrary rational second-hidden-layer neuron
`σ(w·Φ(x))` over the features `Φ(x) = (x_i, σ(x_i − x_j))`. Caterpillar
functions are the special case of an integer head with sum 0 and unit weights.
Example (`inputs/max5_general4.json`, from
`research/sN/dfs/h4-general-neurons/r2_spec_N5_k4.py`):

```json
{"coef": "-1", "head": [0, "1/2", "-1/2", "-1/2", "1/2"],
 "pairs": [[0, 1, "1/2"], [0, 2, "-1"], [1, 2, "1/2"], [1, 3, "-1/2"], [1, 4, "-1/2"], [3, 4, "1"]]}
```

Each instance proves the following.

* `identity`, `max_identity`: `Maximum N x = rhs x` on all of `ℝ^N`, where
  `rhs` is the explicit formula.
* `max_network` (when all `aux` kinds are `lin`/`pair`):
  `∃ net : Network N (firstWidth N) (#units + 2), (∀ x, net.eval x = Maximum N x) ∧
  net.HasRationalWeights ∧ net.HasZeroBiases`. The first hidden layer is the
  paper's layer (`σ(±x_0)`, `σ(x_i − x_0)`, `σ(x_i − x_j)`; `C(N,2)+N+1` neurons).
  The second hidden layer has one neuron per unit and two neurons `σ(±R)` for
  the linear remainder `R`. This comes from the generic
  `SmallN.network_of_expansion` in `Common.lean`, which takes any list of
  `Neuron`s and needs no distinctness or caterpillar condition.

`from_pkl.py` converts an `h5-growth` pickle (`{'N', 'd': {(h, M): coef}}`). It
recomputes the auxiliary coefficients exactly with
`scripts/vocabulary_search.exact_expansion` and checks that the stored unit
coefficients agree. It writes `σ(x_i)` and `σ(−x_i)` with opposite coefficients
as `x_i`. It rejects pickles whose support carries no exact expansion of
`max_N`. For example, `data/sym_5_top_10234.pkl` (42 units, "top" mode) matches
only the top Möbius row, so it is rejected.

## The cover (what Lean checks)

1. **Braid chambers.** An insertion-sort decision tree of
   `rcases le_total (x a) (x e)` splits places each coordinate in turn. The
   value 0 is included as a pseudo-coordinate when some term is not
   translation invariant. Each leaf is a closed chamber
   `x_{π0} ≤ … ≤ x_{π(N-1)}`. Every consecutive inequality of the chamber is
   literally a hypothesis on its path, so no global coverage argument is
   needed.
2. **Cells.** On a chamber, every inner `σ(x_i − x_j)` is linear, so each
   outer argument is a linear form `L_k`. A second tree splits with
   `rcases le_total 0 (L_k)` on the first `L_k` whose sign is not constant on
   the current cell. Cells are kept as exact V-descriptions (double
   description in the chamber's gap coordinates). The sign test is therefore
   exact, and both halves of every split have nonempty interior.
3. **Cell lemma** (`cellC_L`). Its hypotheses are the H-description of the
   cell: the chain `c0 … c_{d-1}` and the splits `s0 …`. The proof:
   * the hypotheses `qj : σ(x_a − x_b) = x_a − x_b` or `= 0` (proved in the chamber);
   * `have ok : σ(outer_k) = outer_k or 0`, with the side condition closed by
     `rw [qj …]; linarith only [cell hypotheses]`;
   * `unfold rhs; linear_combination Σ(−d_k)·ok + Σ μ_j·qj`. The multipliers
     `μ_j` are computed by the generator, and `ring1` checks the result.
4. **Chamber lemma** (`chamberC`) rewrites `Maximum` to the top coordinate
   (`max_eq`). It proves the inner facts `qj` once for the whole chamber and
   passes them to the cell lemmas, then runs the cell tree. The root theorem `identity` runs the
   braid tree.

The generator also checks every cell identity in exact rational arithmetic
before emitting it. It writes the full cover (chamber orders, inner-function
signs, H-descriptions, and outer sign patterns) to `out/<name>_cover.json`.
Output files are split into chunks of at most `--chunk` cells; the root module
is the thin aggregator.

## Instances

| input | N | neurons | chambers | cells | chunks | network widths |
|---|---|---|---|---|---|---|
| `inputs/max4_smallarity.json` (`SmallArity.max_four_identity`, pipeline test) | 4 | 3 | 24 | 28 | 1 | (11, 5) |
| `inputs/max5_general4.json` (`h4-general-neurons/r2_spec_N5_k4.py`) | 5 | 4 general | 120 | 152 | 2 | (16, 6) |
| `inputs/max5_lns27.json` (`h5-growth/data/lns_5_full_1.pkl`) | 5 | 27 caterpillar | 120 | 378 | 7 (`--chunk 64`) | (16, 29) |
| `inputs/max5_asm40.json` (`h5-growth/data/assembled_5.pkl`) | 5 | 40 caterpillar | 120 | 613 | not generated (`--dry` only) | (16, 42) |

`scripts/smalln/build.sh Name` builds one instance module by module and logs
the wall time and peak memory of each module to `out/build_Name.log`. Set
`JOBS` to build cell chunks in parallel. A cell with 27 neurons costs about
10 s, mostly in `ring`; a cell with 4 neurons costs about 1.4 s.
