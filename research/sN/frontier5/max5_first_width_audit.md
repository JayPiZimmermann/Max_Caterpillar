# Independent audit of the matched Max5 first width

Status: 29 October 2026. The minimum first hidden layer width is exactly
**nine**, allowing every finite second hidden layer width and arbitrary
real weights and biases, for ordinary two-hidden-layer ReLU networks
without skips. No gap was found in the current mathematical/certificate
proof. The construction at `(9,14)` attains first width nine; this does
not assert that fourteen is the best second width there.

The recent general bound `6*h1 >= 3*n*n-11*n+12` has a shorter proof,
not a larger numerical value. At n=5 it gives only h1>=6. The stronger
specialized minimum nine was already established by the chain below.

## Lower-bound proof and coverage

1. Remove all biases by homogeneous recession, preserving widths and
   exactness on all real inputs. Split first rows by positive, negative,
   and zero coordinate sum. Both signed classes are nonempty.
2. The local three- and four-coordinate restrictions C3/C4 require at
   least five nonzero invariant first features. With five, exact support
   enumeration leaves three support types. If either signed class is a
   singleton, diagonal translation gives `Max5=ell+Phi(invariant features)`.
   All coefficient-sign classes violate its feature-fiber equations.
   Hence a singleton signed class needs at least six invariant features.
3. At total first width eight, the only possible row-count split is
   `(1,1,6)`. Complete six-feature support/sign classification forces the
   natural bowtie: a signed coordinate anchor, four comparisons to that
   anchor, and two disjoint leaf comparisons.
4. Restricting the anchor input to zero leaves the product of two clipped
   two-input feature images. The rectangle of curvature scores vanishes
   on every finite signed shallow sum over this image, while the target
   has rectangle score one. Thus this first layer has no finite second
   hidden layer completion. Width eight and every smaller width are
   excluded.

The detailed sources are `../frontierN/overnight_general.md`,
`../frontierN/overnight_general_six.md`, and
`../best5/overnight_fixed_natural8_rectangle.md`.

The real-coefficient bridge is essential. Lexicographic inputs use a base
chosen sufficiently large for each fixed real dictionary. Active signs
depend on the leading nonzero coefficient, so the finite sign partition
covers irrational and arbitrarily small nonzero coefficients. Exact
support changes cover actual zeros, and the six-row enumeration includes
support multisets. No bounded coefficient grid or generic-position
assumption enters the exclusion.

The six-row checker uses modular arithmetic only for matrices with at
most six columns and entries zero or one, including augmented systems.
Every minor has absolute value at most `6!=720`, below the prime 1009;
therefore all its rank and forced-equation conclusions are exact over the
rationals. It does not apply modular arithmetic to unknown real weights.

The rectangle argument was reread independently. The b/e coefficient
class is intrinsic on each full four-dimensional corner; normalization
removes proportional-normal ambiguity. Crossing hyperplanes have
independent gradient-jump coefficients at generic points, and fixed-sign
gates have zero score, including boundary cases. The rectangle identity
is termwise and therefore permits arbitrary signed cancellations and
arbitrary finite second width.

Fresh copies of both independent classification checkers passed. Their
sources and data were copied to temporary directories so historical
receipts were not overwritten. The new hash-pinned replay is
`max5_first_lower_replay.json`. It checks all five-feature sign classes
and the complete six-feature support/sign coverage.

The complete network theorem is a mathematical proof with exact finite
certificates. It is not a newly Lean-verified or production-integrated
theorem. Existing Lean checks cover some analytic bridges and the score
algebra, not the complete first-layer classification.

## Independent upper-bound replay

The explicit rational network has seven invariant first features and a
signed coordinate pair, followed by twelve correction neurons and a
signed pair implementing the linear head. Thus its physical widths are
exactly `(9,14)`, with no uncounted linear skip.

A separately delegated audit replayed the exact physical checker and
the comparison-based checker, covering all augmented braid cones and
all ordinary input-order cones. Both passed. See
`max5_first_upper_audit.md`, `max5_first_upper_physical_replay.json`, and
`max5_first_upper_comparison_replay.json`.

## Equality constraints useful for the next construction search

At first width nine, the only possible row-count splits are `(1,1,7)`
and `(2,2,5)`. The proof in `../best5/overnight_fixed_first9_splits.md`
correctly strengthens the singleton restriction: even with arbitrarily
many opposite-sign carriers, six invariant features force the same bowtie
under the singleton translation tail and are excluded by the rectangle.

**First-feature independence.** Every width-nine solution has nine
linearly independent first-feature functions after recession. Otherwise,
solve a nonzero relation for one feature and substitute into every second
preactivation. Deleting that feature would yield an exact width-eight
network, contrary to the lower bound. Consequently there is no zero row,
no positive-proportional duplicate row, and no zero outgoing column.
These conclusions also hold for the weights of a biased original after
removing its biases.

For homogeneous ReLU features, this independence has a precise geometric
form. Group first rows by their unoriented hyperplanes and normalize any
opposite pair to r and -r. A relation among features must cancel curvature
separately on each hyperplane. Hence unpaired features have coefficient
zero, paired coefficients are opposite, and the remaining relation is a
linear relation among the paired covectors r. Thus those paired covectors
must be linearly independent. For coordinate differences, the graph of
opposite-root pairs must be a forest. This supplies a cheap exact filter
for dictionary searches.

**Singleton carriers.** In split `(1,1,7)`, normalize the positive carrier
to p with coordinate sum one and the negative carrier to -m, also with
coordinate sum one for m. If p differs from m, choose x so that m(x)>p(x).
On the interval `-m(x)<t<-p(x)` both carriers vanish at x+t*ones and every
invariant feature stays fixed, while Max5 changes with t. Therefore p=m:
the carrier pair is exactly signed theta in the recession network.
The residual-plus-two theorem then applies with its full hypotheses.

**The five-cycle carrier shift.** In the pure-root `(2,2,5)` branch,
`cycle_contrast.md` forces all four signed carriers into one common
two-coordinate plane. Their normalized within-sign contrasts are
therefore collinear. For second neurons free at both diagonal ends, the
difference of the two tail intercepts has rank at most one across all
such neurons. This sharpens the rank-at-most-two bound available for a
general `(2,2,5)` dictionary; it does not itself exclude second width four
or five.

## Restricted pure-root seven-feature catalog

`max5_first_root7.py` enumerates all seven distinct oriented coordinate
differences, imposing C3/C4 and feature independence, then solving every
braid-cell equation

```
e_winner-theta belongs to span(active coordinate differences).
```

For root features the span condition is exactly the component-sum
equation. All strict braid orders are included. Conversely, the general
single-layer observability theorem proves sufficiency: first-feature
fibers are convex, and this condition makes `Max5-theta` constant on
each fiber, including boundaries by continuity.

The producer gives **sixteen dictionaries up to input permutations**:
four with fixed carrier, eleven with one carrier direction, and one with
two carrier directions. The explicit records are in `max5_first_root7.json`.
A separate simultaneous enumeration by the facet-combinatorics agent
found the same counts; its files are `max5_facets_root7_inventory.py/json`.
`max5_first_root7_cross_check.json` verifies equality of all sixteen
canonical dictionaries, their full component equations, particular
carriers, direction bases, and orbit sizes, and records both source/data
hashes. A further independent implementation checks the sixteen survivors
using descending input orders, direct active-row nullspaces, and exact
Boolean-input feature-rank witnesses, rather than the producer's
component equations. Its proof and receipt are
`max5_first_root7_audit.md`, `max5_first_root7_audit.py`, and
`max5_first_root7_audit.json`.

In each of the sixteen records, theta is a coordinate anchor plus exactly
the span supplied by opposite-root pairs in the invariant dictionary.
Let V be the invariant dictionary span. Changing theta from its coordinate
anchor changes the residual target by an element of V. Since residual
complexity allows a free term in V, that change leaves the minimum number
of residual outer ReLUs unchanged. The exact residual-plus-two theorem
therefore makes the minimum second width independent of these continuous
carrier parameters. Width optimization in this entire restricted sector
reduces to the sixteen canonical-anchor dictionaries.

This is an information and minimum-width reduction. It neither supplies
a finite shallow completion of every catalog entry nor proves a
continuous path between arbitrary completions. It does not cover nonroot
seven-feature dictionaries or the `(2,2,5)` split.
