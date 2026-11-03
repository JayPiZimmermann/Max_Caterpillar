# Exact zero-core conditions at triple contacts

Status: Lean verified by the targeted replay recorded in `receipt.json`.
This is a necessary condition for a representation, not a new numerical
width lower bound or a completed exclusion of Max5(9,4).

Suppose, on every real input,

```
MAX5(x) = R(x) + ReLU(g(x)) + ReLU(h(x)),
```

where each of R, g, h is an affine function plus a finite real linear
combination of ReLUs of affine functions. Every width, coefficient, and
bias is arbitrary; the three functions may use different feature spans.
Then for every distinct i,j and every a,b>0,

```
g(-a e_i-b e_j)=0  or  h(-a e_i-b e_j)=0.
```

Thus the condition holds at all ten pair-contact points (-e_i-e_j),
and along every open segment -t e_i-(1-t)e_j, 0<t<1. These are the
three-way top faces normalized so that the tied coordinates equal zero.
The theorem does not assume positive homogeneity of R, g, or h.

The proof uses local odd linearity: every shallow function has a locally
linear odd part. Where a continuous core is nonzero, its outer ReLU is
locally either that core or zero, and therefore also locally odd-linear.
If both cores were nonzero at the displayed point, MAX5 would have a
locally linear odd part there. The existing three-way-top-tie obstruction
rules this out. A proved input-rescaling lemma extends the old unit-gap
obstruction to every positive gap.

`TripleContact.lean` contains:

- `exists_zero_core_at_top_tie`: the same zero-core necessity for any finite
  number of outer folds with arbitrary signed output coefficients, under
  explicit continuity and local odd-linearity assumptions.
- `max5_pair_contact`: the explicit affine-shallow version at the ten
  pair contacts.
- `max5_weighted_pair_contact`: the explicit affine-shallow version for
  arbitrary a,b>0, hence the whole open segment.

`Statements.lean` independently re-elaborates the exact expected types
of these three declarations. Their transitive axioms are precisely
`propext`, `Classical.choice`, and `Quot.sound`.

Run from the repository root:

```
python3 research/sN/max5_optimal_20261103/lower/triple_contact/verify.py --replay
```

The verifier builds the existing dependency target, recompiles the new
leaf, checks the exact-type consumer, rejects prohibited source constructs
through the local import closure, and records content hashes. This is a
bounded dirty-tree research receipt; the artifact has not been added to
the repository-wide public theorem manifest or aggregator. The recorded
closure contains 78 local Lean sources, including the two new sources.
The imported 76 existing Lean sources and three toolchain/build-control
files all matched the publication checkout byte-for-byte at handoff.

For the support-exclusion application, the additional geometric reasoning
that forces both core values to be negative must be supplied separately.
This file alone does not formalize a support classification or that
midpoint calculation.
