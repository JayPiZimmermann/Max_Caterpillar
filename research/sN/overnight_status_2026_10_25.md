# Overnight proof search: checkpoint at 01:25 UTC

The search remains active. The unrestricted canonical all-tree exponential
lower bound and a uniform exponential exact construction are both open.
Unmatched small-arity experiments stay outside the paper. The paper's finite
width result is the matched second width six for its specified first width ten.

## Uniform lower bounds added tonight

The weighted pseudoforest argument now uses independent witnesses from a
matching, rather than a connected-subtree count. With matching size nu and
z isolated vertices, its tied-set coverage is bounded by
Pr[Bin(nu+z,1/4)<=2]. It allows arbitrary real heads, weights, output signs
and biases. It gives the stronger bounded-degree rate
Omega_Delta((4/3)^(N/(Delta+1))/N^2), and also counts distinct comparison
graphs. See `trees/overnight_pseudoforest_matching.md`.

The same proof now allows edges beyond a spanning pseudoforest. If every
graph has nu+z>=k and at most b such extra edges, the denominator becomes
Pr[Bin(k,1/4)<=b+2]. In particular k=Omega(N), b=o(N) still gives an
exponential bound with no degree restriction. A mixture version retains
the caterpillar and rooted-star face dictionaries. See
`trees/overnight_bounded_excess.md`. All simple graphs through six vertices
and all their vertex subsets passed the exact combinatorial controls.

The paper contains these uniform results, is rebuilt at 42 pages, and has
no overfull boxes or undefined references. The new graph results are
mathematical proofs, not Lean theorems. They do not close the remaining
small-matching tree regime.

## Unrestricted canonical trees

The existing uniform polynomial lower bound is binom(N,4)/35 for N>=7.
The separate N9 exact row campaign is still running: 1,080 of 1,971 rows
have passed two independent rational evaluators and all stored relations.
Only a completed certificate would improve this to binom(N,5)/126.
No completed N9 claim is made here.

The sparse signed-root candidate Q_* has passed 48 additional fixed-apex
grafting gates, but its descent to the full rational-function quotient is
unproved. A new full N9 gate including perfectly matchable trees is being
inventoried separately from the immutable exact-row campaign.

Several proposed functional mechanisms have exact counterexamples. In
particular, a common odd-root-current construction fails a five-label
relation, and the leading near-integer twisted-periodization field of a
star already equals a nonzero multiple of the target. The complete
periodization exhibits the same collapse numerically; that stronger
identity has not been promoted to an exact claim.

## Exponential construction

Common-ghost products of triangle boundaries fail exactly at six labels,
even with all independent reflections and all permutations. Independent
attachment vertices repair that obstruction under full permutation
averaging, but the one-page fixed-order family still fails exactly.

A genuine two-page fixed-order family has an exact positive boundary-lift
identity at six labels. Its compact certificate uses eight dihedral product
orbits. This is a chain boundary lift with nonzero augmentation, not an
emitted network or a uniform construction. The simplest exterior-ear
extension has a seven-label diagnostic obstruction; finite translation
corrections are the next test. The compact replay is
`trees/overnight_upper_two_page_witness.py`.

## Width frontier

The fixed first width nine result remains only 6<=h2<=14 and stays in
research notes. General second width six at five inputs is still open.
The structural branch has a proved two-winner rigidity lemma and exact
selector obstructions. The corrected three-neuron selector pattern is now
excluded even with an arbitrary first hidden layer: a wall-removal argument
reduces it to a 56-parameter span, and 34 exact equations give 0=1.
This excludes one activation pattern, not all three-neuron cores.

## Checkpoints

Stable lower and upper research packages, the selector lemmas, and the new
uniform graph proofs are committed. The latest paper and research commits
through `7e074e3` are pushed. Active exploratory files and large regenerable
caches are not included by broad staging. Historical frozen notes retain
their original status; this file records the current distinctions.
