# Max5 width five: multiple carriers and the exact balanced-four residual

Status: 31 October 2026. No unrestricted width-five exclusion or
construction has been obtained in this branch. The current unrestricted
second-width interval remains four through six.

Two later exact results strengthen declared subfamilies:

* For the bowtie's two specified signed-sum positive core directions,
  the minimum number of negative folds is **three**, even when the
  negative directions range over all of V. The matching identity and
  independently checked lower-bound proof are in
  [bowtie_positive_pair_negative_minimum.md](bowtie_positive_pair_negative_minimum.md).
* Root7 record 11 with a positive singleton carrier needs physical second
  width at least **six**, regardless of the opposite-sign carrier rows.
  The general common-affine-carrier transfer and the necessary sign
  asymmetry are proved in
  [root7_record11_carrier_audit.md](root7_record11_carrier_audit.md).

The broader fixed-positive program, including its 55 exact pair orbits
and arbitrary negative directions, is tracked in
[fixed_positive_pairs.md](fixed_positive_pairs.md).

## A single exact target for all comparison-invariant first dictionaries

Let V be the span of the ten coordinate-comparison ReLUs and the four
linear coordinate differences. The completed three-core theorem says that
Max5 minus an anchor cannot equal a remainder in V plus three folded
functions from V.

Consequently, a physical width-five network whose invariant first rows
are coordinate differences has exactly one passing neuron at each common
translation end, and four effective free neurons at each end. The passing
neurons are distinct, with opposite output signs. There are no zero output
coefficients. Each tail is an irredundant four-core identity in V.

The only physical output counts are two positive and three negative, or
three positive and two negative. In the first case the negative tail is
balanced, with two positive and two negative free folds. In the second
case the positive tail is balanced. Therefore the following single
statement would close this entire class at every first width:

> No exact Max5 residual identity over V uses two positive and two
> negative folds, with a free remainder in V.

This is a sufficient lower-bound target, not an established exclusion.
The existing independently certified 75-atom exclusion covers only a
finite family of core directions. Its scope cannot be enlarged to V.
The detailed tail proof is in [rootinvariant_width5_overlap.md](rootinvariant_width5_overlap.md).

The signed-shift identity also implies that the three common-free shifts
have nonzero joint rank. Their rank is at most the number of positive-sum
first rows plus the number of negative-sum first rows, minus two. Rank
zero would reduce the network to the already excluded three-core case.
One signed class being a singleton does not itself eliminate shifts from
the other class.

## Complete arbitrary-real software for the balanced residual

`research/sN/frontier5/max5_exact_fourcore_full.py` implements the exact
four-core comparison-space problem, rather than a finite coefficient or
atom search. It has 70 real variables: fourteen coefficients for each of
four cores and fourteen for the free remainder.

The thirty proper Boolean rays determine each V function on the 120
braid chambers. The formula requires the target value on those rays and
zero interior curvature on every chamber. A partition groups each
crossing preactivation with all other preactivations on its same zero
hyperplane. Each group has collinear chamber forms and zero signed
curvature. All two-, three-, and four-element groups are retained. The
balanced sign case has twelve allowed partitions per chamber.

These conditions are necessary and sufficient: cancellation makes the
represented function affine on each chamber, and the ray equalities then
identify that affine function with the target. In particular, the
three-core pair-cancellation theorem is not applied beyond its scope.

Additional necessary local constraints require a common zero core along
each generic triple-top-tie sector. A four-way tie has a positive zero
core or at least two negative zero cores. If exactly one core vanishes
at a four-way tie, it is positive and its local germ is the difference
of complementary pair maxima. These consequences use the previously
audited one-core Max4 classification.

Independent audit: [fourcore_model_audit.md](fourcore_model_audit.md).
The known exact bowtie, converted to the same fourteen-coordinate basis,
passes the full model including the local constraints. This is a control
for the implementation; it is not evidence for a balanced construction.

The companion `max5_exact_fourcore_irredundant.py` adds two consequences
of the completed three-core exclusion:

* Every core has a strictly positive and a strictly negative Boolean-ray
  value. Otherwise its folded function belongs to V and is absorbed by
  the remainder.
* No pair of global core coefficient vectors is proportional. After
  complementing one orientation and adjusting the remainder, such a pair
  consolidates into at most one fold.

## Computation status and remaining scope

The initial full balanced and one-positive/three-negative probes, and a
pair-only diagnostic, each returned UNKNOWN at 120 seconds. The enhanced
full balanced model returned UNKNOWN at 180 seconds. The independent
cvc5 probe of that same frozen formula and the irredundancy-strengthened
Z3 probe also returned UNKNOWN at 180 seconds each. These are recorded
timeouts, not exclusions; their separate receipts are beside the scripts.
A further wrapper additionally fixes the local shallow remainder in
each unique-positive-core four-way-tie branch, using the same comparator
rigidity theorem. Its known bowtie control passes, and its full balanced
probe also returned UNKNOWN at 180 seconds. The separate branch in which
all four cores vanish at all five four-way-top-tie rays returned UNKNOWN
at 180 seconds. The separately normalized unique-four-way-tie branch
also returned UNKNOWN at 180 seconds. None of these timeouts proves a
branch empty.

The sixteen seven-root dictionaries give smaller exact subproblems. A
singleton diagonal carrier makes every free core in that tail depend
only on the invariant features. Excluding four-core residuals in all
sixteen dictionaries would therefore also rule out the first-width-ten
splits with one positive carrier, two negative carriers, and seven
invariant rows, and the sign-reversed split. The P4 instance was already
known; the other instances require their own certificates.

## The remaining six-root support graphs at first width ten

In the row-count split with two positive carriers, two negative carriers,
and six invariant rows, assume every nonzero invariant row is a coordinate
difference. Let G have the five input labels as vertices and one
undirected edge for every distinct comparison hyperplane. The established
C3 support condition says that G has no independent triple. C4 says
every vertex has at least two neighbors: if a vertex had three
nonneighbors, the four-set consisting of those vertices would violate
C4 at that vertex.

The complement of G therefore has maximum degree two and contains no
triangle. There are at most six distinct edges in G. If there are six,
its complement has four edges on five vertices and must be either the
five-vertex path or a four-cycle plus an isolated vertex. Thus G is,
respectively, a five-cycle with one chord or the bowtie consisting of
two triangles sharing one vertex. If G has only five edges, it has
minimum degree two and hence is a five-cycle. Fewer than five edges are
impossible. Repeated orientations and zero rows are retained in this
last support case; no functional-independence assumption is needed.

At either tail the two same-sign carriers contribute at most one
invariant linear contrast to a free preactivation. Thus the four free
preactivations lie in the span of the six invariant features and at most
one linear contrast. Relative to a fixed coordinate anchor, the shallow
remainder can additionally contain the normalized passing carrier minus
that anchor; it must not be discarded without a separate argument.
This leaves a small list of oriented support
graphs with a continuous contrast, rather than an arbitrary
fourteen-dimensional comparison span. The graph reduction is exact;
the needed four-core exclusions for these continuous contrast spaces
remain open.

Arbitrary nonroot invariant directions remain outside the comparison
space. Moreover, an unrestricted width-five search at first widths ten
through twelve must retain the four-positive/one-negative output sector:
the existing first-width-thirteen obstruction excludes a unique positive
output, but does not exclude a unique negative output.

No Lean files were changed. No completed model, necessary condition, or
solver timeout is asserted to settle the unrestricted Max5 minimum.
