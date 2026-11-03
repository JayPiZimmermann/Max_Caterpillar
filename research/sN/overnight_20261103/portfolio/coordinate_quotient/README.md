# Coordinate identification: exact network transport

The Lean development proves a model transformation, together with two
transported lower bounds. It also proves why this criterion is **not stronger
than the optimal support-transversal criterion**.

For a surjection `φ : Fin N → Fin m`, substitute `x_i = y_(φ i)` in the
original affine-skip network. Replace each input covector by its block sums:

    A'_(j,b) = sum_(i: φ i = b) A_(j,i).

Do the same for the input-to-second-hidden covectors and the input-to-output
covector. Preserve all first and second hidden indices, biases, remaining
weights, and output skips. `Model.eval_quotient` proves exact evaluation on
every real input. `quotient_computes_max` proves that an actual MAX_N identity
becomes an actual MAX_m identity; surjectivity is necessary.

If every original zero-bias, zero-sum first row has at most two nonzero block
sums, faithful normalization gives an actual braid-first-layer MAX_m model.
There is no assumption on the first hidden width. The imported, already
proved five-input obstruction then gives

    h2 >= m² / 3,000,000,  for m >= 3.

`Bounds.conditional_affine_quotient_lower_bound` also transports the existing
conditional growing-matching result. Its local matching obstruction `H`
remains an explicit, generally unproved hypothesis. This file proves no new
unconditional exponential lower bound.

## Why coordinate identification does not improve the optimal deletion size

Choose one representative in each fiber of `φ`. A covector supported on
these representatives has no cancellation when block-summed: the resulting
coefficient in each block is exactly the coefficient at its representative.
Thus a braid quotient of dimension m always supplies a valid generic retained
coordinate set of size m. `Section.exists_braid_retained_of_quotient` proves
this implication in Lean, rather than leaving it as an informal scope note.

The coordinate quotient remains a useful explicit model transformation and
an alternative way to construct usable restrictions. It must not be counted
as a separate improvement to the unrestricted width bound.

## Verification

`Check.lean` expands evaluation into the nine primitive parameter arrays and
checks the quadratic statement with the literal block-support predicate.
It includes an exact MAX_2 network under the noninjective map to one input,
and a countercontrol showing why a nonsurjective map need not preserve MAX.

Run:

    python3 research/sN/overnight_20261103/portfolio/coordinate_quotient/recheck.py --run

The receipt records source/control hashes and exact-type/axiom checks. These
are isolated research modules, not additions to the frozen public roots.
