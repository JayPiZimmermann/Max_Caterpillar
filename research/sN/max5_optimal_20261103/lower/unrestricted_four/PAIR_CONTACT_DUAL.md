# Exact two-coordinate dual lemma

Status: Lean verification of the finite-vector statement below. This leaf
does not formalize the convex-core network argument or improve the MAX5
width endpoint.

Let `a,b` be real vectors on any finite index type, each with coordinate
sum zero. Suppose no nonnegative combination of two coordinate pairs
`(a_i,b_i),(a_j,b_j)` is strictly negative in both coordinates. Then

```
a=0, or b=0, or b=-c*a for a real c>0.
```

Conversely each of those three alternatives satisfies the contact
condition. Repeated indices, zero weights, zero coordinates, and the
empty index type are included. Thus the statement does not silently
assume genericity or exclude boundary cases.

The main declarations in `PairContactDual.lean` are
`negatively_proportional`, `zero_or_negatively_proportional`, and
`noNegativePair_iff`, in namespace `MaxCaterpillar.Max5.PairContactDual`.
`PairContactDualCheck.lean` states the entire hypothesis literally and
checks a nonzero two-coordinate example `(1,-1),(-1,1)`.

The proof is elementary. A nonzero zero-sum vector has a negative
coordinate. If `a_i<0`, the pair condition and a negative coordinate of
`b` force `b_i>0`. Choose a negative coordinate `p` minimizing
`b_p/(-a_p)`. Ratio comparison handles every other negative coordinate
of `a`. At a nonnegative coordinate of `a`, a negative determinant
`b_p*a_i-a_p*b_i` explicitly supplies a forbidden nonnegative pair.
Consequently this determinant vector is coordinatewise nonnegative.
Its sum is zero, so it vanishes identically, giving the conclusion.

The Lean proof uses rational arithmetic and finite sums over real
variables; it does not call a numerical solver or an external certificate
checker. Its recorded axiom sets are contained in `propext`,
`Classical.choice`, and `Quot.sound`.

Rebuild the producer and exact-type consumer from the repository root:

```sh
python3 research/sN/max5_optimal_20261103/lower/unrestricted_four/pair_contact_dual_recheck.py
```

The script writes a source-bound receipt and durable exit markers. Its
repository-local Lean import closure has two files; external Mathlib and
Lake packages are pinned by the repository's manifest and toolchain.
