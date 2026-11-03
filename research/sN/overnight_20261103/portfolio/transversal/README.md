# A support transversal replaces the first hidden width assumption

For an exact real affine-skip network computing MAX_N, let C be a set of
input coordinates. Suppose every original first-hidden row with all three
properties

* its bias is zero;
* its coordinate sum is zero;
* at least three coefficients are nonzero

has a nonzero coefficient at a coordinate in C. Put m=N-|C|. Then, for m>=3,

    h2 >= m² / 3,000,000.

There is **no assumption on h1**. All real signs, second-hidden linear heads,
first-to-output skips, output linear terms, and biases are permitted. The
conclusion counts the original second-hidden indices. This is a structural
relaxation: a small transversal can exist even with arbitrarily many first
rows. An arbitrary collection of supports need not admit a small transversal,
so this does not improve the worst-case exponent as a function of h1 alone.

The condition may be strengthened to hit every zero-sum row of support at
least three, regardless of bias. The displayed weaker condition is sound
because the imported normalization uses an exact directional model at the
origin, and only zero-bias rows remain nonlinear there.

## Proof and Lean declarations

`Model.exists_braid_model` constructs the normalized model at any retained
coordinate embedding. The existing actual-network normalization retains a
first row precisely when its original bias and coordinate sum both vanish.
At a generic top tie on the retained coordinates, every remaining row whose
support leaves that set has a nonzero base value and becomes affine. Every
surviving row therefore has at most two nonzero coefficients. Genericity is
proved by the imported tied-point construction; it is not a hypothesis.
Both original hidden index sets and original feeding lineage are preserved.

`Bounds.normalized_braid_quadratic` obtains the explicit quadratic constant
from the already proved five-input, two-disjoint-edge obstruction. In the
finite transfer both non-braid support costs vanish. The existing cutoff
theorem gives h2 >= (N-5)²/2,163,200 for large N; the original linear width
bound covers small N. This yields the uniform constant above without any
first hidden width hypothesis.

`Bounds.affine_transversal_quadratic` constructs the complement embedding
and proves the displayed raw-network theorem. The namespace is
`MaxCaterpillar.Overnight.SupportTransversal`.

`Bounds.conditional_affine_retained_lower_bound` also transfers the existing
growing-matching braid theorem. If H(4q+1,q) holds, q>=1, and 160000 q²<=m,
then h2 >= (23/25) 4^q. **H remains an explicit unproved hypothesis for
growing q.** The reduction itself does not prove an exponential lower bound.

## Verification

Run:

```sh
python3 research/sN/overnight_20261103/portfolio/transversal/recheck.py --run
```

The checker rebuilds the production imports and the three research leaves,
checks expanded nine-array and literal-transversal statements, checks an
actual exact MAX3 network, audits standard axioms, and binds all source and
control hashes. The authoritative status is `receipt.json`; these research
leaves are not automatically integrated into the production root.

Output-only first neurons are currently included in the transversal
condition. A feeding-only version requires a separate absorption argument;
it is not silently asserted here.
