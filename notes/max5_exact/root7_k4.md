# Max5: four-correction exclusions for seven-root first layers

Status: 31 October 2026. These are exact lower bounds for declared first
hidden layers. They do not determine the unrestricted optimal Max5 width
pair. No Lean files were changed.

## Completed result

In the sixteen-case catalog of first layers with seven invariant
coordinate-comparison features and one signed carrier pair, **seven
classes require at least seven neurons in the second hidden layer**.
The zero-based catalog indices are

```
0, 1, 2, 3, 4, 8, 9.
```

Class 1 is the earlier fixed-P4 theorem. The other six classes are new
exclusions of every four-correction representation. All thirty new
refutations, covering five possible positive-output counts for each
class, have independently passed Ethos replay against their original
SMT formulas. The mathematical model has a separate independent audit.

The catalog is
[max5_first_root7.json](../../research/sN/frontier5/max5_first_root7.json).
The [combined manifest](../../research/sN/frontier5/max5_nov01_root7_k4_manifest.json)
copies the exact seven directed rows and carrier anchor for every new
class and pins the source, proof, and replay hashes. Its status is
`ALL_30_INDEPENDENT_ETHOS_PASS`.

The present restricted width table is therefore:

| Root7 catalog classes | Lower bound on the second hidden layer |
| --- | ---: |
| 0, 1, 2, 3, 4, 8, 9 | 7 |
| 5, 6, 7, 10, 11, 12, 13, 14, 15 | 6 |

The second line uses the completed comparison-space residual lower
bound four and the signed-carrier cost theorem. It is a lower bound,
not an assertion that these dictionaries admit six-neuron completions.

## Exact reduction and proof

Let W be the span of the seven comparison features, and let xa be the
catalog's coordinate anchor. The existing carrier-elimination theorem
reduces every admissible carrier in that class to xa without changing
the minimum width. The exact physical second width is two plus the
minimum number of correction terms in

```
Max5 - xa = R + sum sign_k ReLU(g_k),    R,g_k in W.
```

Suppose four corrections suffice. Absorb every nonzero output magnitude
into its preactivation and allow zero preactivations. Twice the identity
becomes

```
2(Max5-xa) = B + sum sign_k abs(g_k),
B = 2R + sum sign_k g_k.
```

B is an arbitrary element of W. The necessary equations are:

1. Thirty values on nonempty proper Boolean subsets.
2. Twenty generic three-way top-tie mixed differences.
3. Five four-way top-tie mixed differences.
4. The full five-way mixed difference at the origin.

At a generic top tie, a correction contributes only when its
preactivation vanishes identically along the relevant top-tie cone.
Those are exact linear equalities in its seven coefficients. Its
contribution is an alternating sum of absolute values of linear forms.
Thus the entire necessary problem is quantifier-free linear real
arithmetic with disjunctions, despite allowing all real, unbounded
network coefficients.

Complementing a correction changes only the shallow remainder, so each
core can be given the producer's orientation gauge. Permuting cores of
the same output sign supplies the harmless ordering gauge. No positive
coefficient margin, rational-weight hypothesis, or generic network
assumption is imposed. Fewer than four corrections are included by
padding zero preactivations. All five sign counts, including four
positive and four negative, are checked separately.

For class 4 with two positive corrections, one additional exact input
equation was obtained from a rejected candidate. This is an ordinary
necessary input-output equality; the search procedure and the candidate
checker are not trusted to establish the final UNSAT result. The input
and emitted original formula are retained. All other completed cases
use the basic locality/Boolean system alone.

The [independent semantic audit](root7_k4_local_model_audit.md) proves
necessity on the full real coefficient domain. Its independent arithmetic
controls cover 5,440 root directional germs and 58 equations of the
known four-correction bowtie identity. CVC5 produces the refutations;
Ethos checks each without trusting the solver. Biases are covered by
taking homogeneous recession at unchanged widths.

Replay the package assembly with:

```
python3 research/sN/frontier5/max5_nov01_root7_k4_manifest.py
```

To repeat proof production and independent replay, use
`max5_nov01_root7_k4_proofs.py` with the desired catalog indices and
positive counts. This can require substantially more time than manifest
validation.

## Additional completed reductions

[Strict feature-space equivalence](root7_equivalence.md) gives sixteen
distinct orbits, so the old P4 certificate transfers directly only to
class 1. Adjoining arbitrary linear functions is invalid: adding just
the direction t-u to the P4 span already permits the known four-fold
identity. This explains why a superficially natural normalization would
destroy the lower bound.

[Positive-facet capacities](root7_positive_capacities.md) prove that
every one of the sixteen dictionaries needs at least two positive
correction gates, regardless of how many negative corrections it uses.
Classes 0, 1, 2, 4, 8, and 9 need at least three positive corrections
by short facet certificates. Class 3 also needs three: its bipartite
incompatibility graph admits 256 proper two-colorings, but every coloring
makes an assigned carrier amplitude vanish after intersecting all its
constraints. An independent exhaustive replay checks all 32,768 binary
assignments. Thus pairwise graph colorability alone misses this stronger
linear-algebra obstruction.

[The two-positive subspace cover](root7_two_positive_span_audit.md)
goes beyond looking for pairwise-incompatible facet triples. Assign
each target facet a positive carrier, enumerate the permitted graph
colorings, and intersect all linear carrier constraints within each
color. This gives eight, one, and five closed subspace pairs for
classes 6, 11, and 13 respectively, up to exchange of the two positive
cores. Every network induces a covered assignment; including zero
amplitudes in the closed spaces only relaxes the necessary test.

In class 11 both positive-core directions are fixed. The resulting
balanced-four problem reduces to a complete linear-arithmetic model:
negative cores can cross inside a first-linear cell only on one of the
known positive-core hyperplanes. Its exact cancellation equations and
Boolean-ray values exclude the two-positive/two-negative pattern.
The implementation is
`max5_nov01_root7_r11_p2_fixedpositive.py`; its trust-free CPC proof has
passed Ethos replay. The
[separate mathematical implementation audit](root7_record11_fixed_positive_audit.md)
passes. A reduced certificate uses just six Boolean inputs and five
braid cones, and its independent Ethos replay passes too. This
sign-pattern exclusion alone does not raise class 11's total-width
lower bound to seven.

The stronger completed
[class-11 positive-capacity theorem](root7_record11_positive_capacity.md)
excludes two positive corrections with **any finite number of negative
corrections**. A linear combination T of six Boolean evaluations
annihilates W and both positive folded directions, while T applied to
Max5-xa equals -1. Every admissible negative fold has T at most zero,
as proved by a seven-variable linear-arithmetic refutation with an
independent model audit and Ethos replay. Applying T to an alleged
identity gives the contradiction. The classes now known to require
three positive corrections are therefore

```
0, 1, 2, 3, 4, 8, 9, 11.
```

## A reusable reduction to linear arithmetic

Fix a finite first-layer dictionary and a finite polyhedral fan on which
its features are linear. Suppose every positive correction direction is
fixed, while its nonnegative magnitude remains variable; let negative
correction preactivations vary freely in the dictionary span. Exact
identity with a target linear on each cone is a finite linear-arithmetic
decision problem with disjunctions.

On one cone, any crossing negative core must be parallel to a crossing
positive core: otherwise its strictly negative curvature has no positive
term that can cancel it. Those positive normals are known. Each negative
core therefore has finitely many choices: fixed nonnegative sign, fixed
nonpositive sign, or a multiple of one of the known normals. Parallelism
to a fixed normal is linear. Each normal's total signed absolute
amplitude must vanish, which is also piecewise linear. Once crossings
cancel, it suffices to match the target on the cone's generating rays
and lineality. Zero amplitudes and boundary sign cases remain included.

The same reduction still works with **one additional freely varying
positive core and one freely varying negative core**. If their crossing
normal is not one of the known positive normals, they must cancel as
an isolated opposite-sign pair, so their linear forms agree up to sign.
If it is known, both are multiples of that fixed normal. Multiple known
positive normals can survive only if the single negative core cancels
each nonzero group, forcing all but one group's amplitudes to zero.
These alternatives are again a finite linear-arithmetic disjunction.

This reduction concerns fixed first features and fixed positive core
directions. It does not turn unrestricted four-core search into linear
arithmetic. The class-11 balanced exclusion is its first completed use
here.

## Remaining obligations

The other nine catalog classes have not been completely excluded at
four corrections. Full cancellation models retain every proportional
three- and four-core group; their bounded solver runs on classes 6,
11, and 13 timed out or remained partial. Necessary-equation SAT
solutions were checked against the original network on all real inputs
and rejected, but those individual rejections do not exclude their
architectures.

For the remaining three-positive/one-negative case in class 11, the
facet-constraint intersection lattice has 77 flats, including zero.
There are 236 covering triples of nonzero flats, and 17 maximal products
of coefficient subspaces cover them all up to positive-core permutations.
The exact producer is `max5_nov01_root7_positive3_cover.py`; the independent
standard-library closure and coverage checker is
`max5_nov01_root7_positive3_cover_check.py`. These are necessary coefficient
families, not feasible networks or fiber components. They reduce the
remaining continuum to seventeen linear-subspace products on which the
full cancellation problem can be tested.

Even a complete resolution of all sixteen classes would leave
arbitrary nonroot invariant first rows and the four-carrier first-width
nine branch. These remain separate parts of the unrestricted Max5
minimum-width problem.
