# Arbitrary-orientation continuation, 24 October 2026

The unrestricted all-tree exponential lower bound remains **open**. The
current unconditional progress removes every edge-orientation restriction
for trees with a matching of linear size, and a separate reduction allows
all orientations of stars. The model still has a canonical head
`x_root-x_apex`, unit edge coefficients, and omitted/linear/hinge states;
it does not allow arbitrary weighted inner edges or arbitrary heads.

## Proved extension

Let `N >= 3`, `0 <= 2k <= N-1`, with integer `k`. Add every tree-face unit
whose original tree has matching number at least `k` to the known
caterpillar/rooted-star face dictionary. Every exact expansion of `max_N`
uses at least `(169/147)^k/(N+1)^2` dictionary units, apart from the
auxiliary remainder. This is a nonvacuous spanning dictionary. All edge
orientations and every face state are permitted for the added trees.

See [the proof and scope](orientation_audit_matching.md) and its exact
finite controls. A positive fraction of nonleaf vertices suffices, since
an n-vertex tree with L leaves has matching number at least `(n-L+1)/2`.
In particular, stars with every edge subdivided once are now covered in
all orientations and all face states. The paper includes the proof.

The independent review checked the top-dimensional-germ-to-passage bridge,
the common integer base for the enlarged finite expansion, and the choice
of a section of the tied-coordinate space. The exact controls enumerate
all 435 unlabelled trees through 11 vertices and 621,273 vertex subsets.
These are controls of the uniform mathematical proof, not a Lean theorem.

## All oriented stars

See [the coordinate-deletion proof](orientation_audit_stars.md).
Successive opposite-face differences reduce any oriented star to smaller
oriented stars modulo the lower-dimensional filtration. They send the
maximum exactly to the lower-arity maximum. Composing with the existing
exact five-label star separator yields a separator at every arity at
least five. This also covers all star face states.

Consequently arbitrary oriented star functions can be added to the mixed
matching theorem. The count of nonstar functions is still at least
`(169/147)^k/(N+1)^4` for `N >= 5`; no bound on the number of added stars
is needed. With just caterpillars and all oriented stars, the sharper bound
is `(7/6)^N/(N+1)^4` on the nonstar terms. Assign every function in the
star family to that class before counting, even if it has another description.
This is a mathematical argument using the independently checked
five-label certificate, not a Lean-verified result.

## New residual: matching deficiency

The script `orientation_matching_probe.py` tests whether the maximum's top
class can be spanned using only trees lacking a perfect or near-perfect
matching. At seven labels, all 258 canonical rooted oriented tree orbits
with matching number at most two give modular ranks **112/113** on 240
frequency rows, prime 1000003, in 21.7 seconds (exit 0). This is **only a
modular diagnostic**. Neither an exact seven-label separator nor a uniform
separation theorem has been proved by that calculation.

The [odd-arity refinement](reopen_lower_odd.md) now needs this separator only
at sufficiently large odd arities. On those ties the nonapex tree must have
a perfect matching, so no unmatched vertex needs to be recorded. A forest
on `N-1` vertices has at most `F_N` matchings by the leaf recurrence.
Consequently the hypothesis, starting at an odd threshold `m0`, would give
`|K| >= (2^(N-1) - sum_(odd j<m0) binom(N,j))/F_N`, with exponential base
`2/phi`, about 1.236, and no polynomial denominator. This remains conditional.

The same note refutes a tempting induction: one fixed coordinate deletion
cannot establish the new odd-arity separator. Duplicate a leaf of an
arbitrary smaller tree as an outward leaf at its hub. The enlarged tree
has no perfect matching, but deleting that new coordinate recovers the
arbitrary original unit modulo `L_1`. Thus its image already spans the
smaller maximum. This is an obstruction to that recursion, not a refutation
of separation. Exact matching and exposed-face controls accompany the proof.
The earlier outward-twin residual remains another sufficient route.

For the separate upper problem, see the [renewed exponential tree families](EXPONENTIAL_FAMILIES.md).
Breadth-first and fixed-hierarchy candidates have exact five- and six-input
top identities, with all roots and orientations and both traversal directions.
The all-arity construction is still open.

## A shortcut refuted for outward twins

The earlier roots-of-unity evaluation failed for the larger all-twin
family. Restricting to outward twins does not repair it. The new probe
`orientation_roots_unity.py 5` already returns a nonzero value 60 on an
outward-star orbit while the simplex has value 1. The modular point is
nonsingular, so reduction of the cyclotomic field proves that the proposed
zero evaluation cannot be an identity over characteristic zero.

There is also a short exact proof for every odd arity m >= 5. Take the
outward star with apex a and centre c:

`U = sigma(x_c-x_a + sum_{l != a,c} sigma(x_l-x_c))`.

Its generic Fourier function, omitting the common nonzero factor, is
`R = (-omega_a)^(m-4) / prod_{l != a,c} omega_l(omega_l+omega_a)`.
Let the frequencies be all m-th roots of unity. Their product is one,
their first and second power sums vanish, and no two are negatives.
Writing `a=omega_a`, the polynomial identity `prod_i(t+omega_i)=t^m+1`
gives `prod_{i != a} omega_i(omega_i+a)=a^(-2)`. Hence
`R = -a^(m-2) c(c+a)`. Summing over `c != a` gives `2a^m=2`.
Summing over a and over the `(m-2)!` leaf permutations gives
`2m(m-2)!`, while the simplex value is one. Thus this single evaluation
fails at every odd arity, even for an outward star. It says nothing
against separation by another functional.

## Reproducibility and publication status

The scripts use the repository research Python environment; the numerical
dependencies are NumPy, SymPy and NetworkX. Exact finite controls use
integer or rational arithmetic. The matching-rank probe has a declared
90-second budget and 240-row cap; its seed sequence is inherited from
`dfs_review_fourier.points`. All substantive outputs and failed routes are
kept beside their producers. The Lean public theorem interface builds,
but the old global 122-statement receipt predates the source consolidation.
The new mathematical extensions have not been added to that manifest.
