# An exact interval recurrence, and the information it cannot discard

The two-component noncrossing upper construction remains open. This note
gives an exact recurrence for its weighted rooted-tree kernels, identifies
the required attachment state, and excludes two simple coefficient rules.

Fix an external parameter `a` and two orientation weights `w_+,w_-`.
For a root-away cut of total frequency `q`, write

\[
E_a(q)=\frac{w_+}{q(q+a)}+\frac{w_-}{q(q-a)}.
\]

For an ordered interval word `I` of frequencies, let `H_a(I)` sum the
products of these edge factors over noncrossing trees rooted at an
additional endpoint immediately before `I`. The root's own frequency
does not occur in any root-away cut. Set `H_a(empty)=1`.

## The planted attachment state

Attaching an external parent to vertex `v` inside an interval does not
permit an arbitrary rooted noncrossing tree on that interval. An edge
with endpoints on opposite sides of `v` would cross the parent edge.
Already on labels `0,1,2,3`, the parent edge `02` crosses the child edge
`13`. The naive three-vertex child count therefore includes two invalid
attachments when its root is the middle vertex.

The correct *planted* state forbids edges straddling its root. It factors
into independent endpoint-rooted trees on the left and right of `v`:

\[
P_a(I,v)=H_a(I_{<v})H_a(I_{>v}).
\]

Deleting the external root of a noncrossing tree leaves consecutive
blocks. Each block has one attachment vertex and one parent edge.
Consequently the exact recurrence is

\[
 B_a(I)=E_a\left(\sum I\right)
        \sum_{v\in I}H_a(I_{<v})H_a(I_{>v}),
\qquad
 H_a(I)=\sum_{\substack{J\text{ nonempty}\\J\text{ prefix of }I}}
             B_a(J)H_a(I\setminus J).
\]

Every right-hand `H` has smaller interval size, so the recurrence is
triangular. A component with root `r` uses `H_a` on the cyclic order of
its other vertices, starting immediately after `r`. A two-component
kernel then multiplies the two component states and the prefactor
`(-a)^(N-4)`, with `a` the total frequency of the second component.

When every edge factor is replaced by 1, the generating function obeys
`H=1+zH^3`. Thus the rooted tree counts are `1,1,3,12,55,...`, as required.
The naive unplanted attachment gives 14 instead of 12 at four vertices.
The producer independently checks all roots of every noncrossing tree
on two through five vertices, using complete Prüfer enumeration and
direct cut products, for weights `(1,0)`, `(0,1)`, and `(2,-3)`.

## A scalar target rule fails at five inputs

First let every first-component edge have positive-away orientation,
and every second-component edge have negative-away orientation. Sum
uniformly over the roots, noncrossing trees, and cyclic intervals of a
fixed component size `p`. Allow an arbitrary coefficient for each `p`.
Complementary component sizes are redundant by input negation, so there
are `floor(N/2)` columns.

At `N=5`, the two columns and the simplex target have exact evaluation
rank three. This proves that no coefficients depending only on component
size can give the desired identity in this orientation restriction.
The rows are exact rational evaluations, and the augmented rank equals
the total number of columns, so this conclusion does not require an
unproved rational-kernel rank upper bound.

## Orientation counts alone also fail

Retain the full orientation polynomial in each component. Its coefficient
of `z^i` records exactly `i` positive-away edges. Permit arbitrary
coefficients depending on `(p,i,j)`: component size, positive-away count
in the first component, and positive-away count in the second. The
coefficients still sum tree shapes, root locations, and embeddings
uniformly.

At five inputs there are ten such columns. Their augmented evaluation
matrix has exact rank eleven. Thus this stronger coefficient rule also
fails. The coefficient polynomials are independently checked against
the same complete Prüfer/cut enumeration by evaluating three signed
orientation-weight pairs.

These are obstructions to discarding information, not exclusions of the
two-component noncrossing dictionary. Any successful recurrence must
retain some further dependence on tree structure, root/attachment
location, or the embedding. The planted visibility state is already
necessary for correct enumeration; the target identity additionally
requires more than a component-size and orientation-count statistic.

Producers and exact finite records:
`overnight_upper_interval_states.py/.json` and
`overnight_upper_interval_polynomial.py/.json`. Both complete in less
than one second in the research environment. The general kernel
recurrence is proved by the unique root-block decomposition above; the
finite controls check its implementation, not its universal validity by
sampling.
