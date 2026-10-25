# Outward twins suffice: a conditional all-tree exponential count

25 October 2026. This is a conditional uniform counting theorem. The
uniform separator hypothesis remains open. It is not an unrestricted
exponential lower bound. The counting proof was independently reviewed.

This sharpens the conditional leaf-pair argument in `all_tree_review.md`
by counting a hub and all its original leaves together. It requires only
outward-twin separation, which is weaker than separation of all trees
without a perfect matching or of all equally oriented sibling leaves.

## Hypothesis and conclusion

Suppose that, at every odd arity m >= m0 for one fixed m0 >= 5, there is
a linear functional modulo L_(m-2) which is nonzero on max_m and vanishes
on every canonical tree unit having two distinct nonroot leaves l1,l2
at one hub v, both carrying σ(x_li-x_v). All apex placements, head roots,
other orientations, and label permutations are included in this hypothesis.

Then every exact expansion of max_N in K canonical tree face functions
and the existing auxiliary shallow span satisfies, for N >= m0 and n=N-1,

    |K| >= [1 - 2^(-n) sum_(odd j<m0) binom(N,j)]
              * (4/3)^(n/3) / n.

In particular the conditional uniform rate is

    Omega((4/3)^(N/3)/N),

with exponential base approximately 1.10064. This is weaker than the
conditional Fibonacci rate from full perfect-matching separation, but
requires a strictly weaker separator. Neither separator has been proved
uniformly. Arbitrary real-head or weighted tree units are outside this
statement.

## The exact necessary leaf rules

Use the existing generic top-tie germ construction, with all outside
coordinates distinct negative superincreasing powers. A contributing
canonical unit must retain its apex among the tied labels: its untied
apex has the uncancellable integer coefficient -1 at a superincreasing
outside base point. The rank bound forces the retained comparison graph
to be connected, with every induced internal edge in its hinge state.
Frozen outside components transport the canonical head to one retained
root. The resulting top germ is another canonical tree unit. All other
germs, and the auxiliary shallow remainder, lie in the lower span.

For a nonroot ORIGINAL leaf l with its original hub v, write S for the
tied original-tree vertices. The canonical head-flow reduction gives:

* An omitted leaf is absent from S.
* A nonroot linear leaf prevents every connected top germ: if outside,
  its frozen coefficient cannot cancel; if inside, its hinge rank is lost.
* For an inward leaf σ(x_v-x_l), membership of l equals membership of v.
* For an outward leaf σ(x_l-x_v), membership of l implies membership of v.
  Two such retained leaves at one hub are killed by the assumed separator.

The inward implication from hub to leaf uses the outside coefficient:
if the tied hub has value zero, an untied negative leaf activates that
hinge with coefficient -1, which has no other incident edge to cancel it.
A retained nonroot original leaf cannot become the transported head: its
only neighbor is retained, so no outside component attaches there. We
therefore remove only the possible ORIGINAL head-root leaf from counting.

## Trees with large matchings

Let ν be the matching number of the original n-vertex tree. For a fixed
vertex r, every connected vertex subset containing r is ancestor-closed
when the tree is rooted at r. Each edge in a matching forbids the pattern
in which its child is selected and its parent is absent. Since matching
edges are disjoint, there are at most

    2^(n-2ν) 3^ν = 2^n (3/4)^ν

such subsets. Summing over r is a valid upper bound for all connected
nonempty subsets. Thus, when ν >= n/3, a unit can cover at most

    n 2^n (3/4)^(n/3)

tied label sets. The apex is fixed and must be included, so it adds no
independent choice.

## Trees with small matchings

Suppose ν <= n/3. A minimum vertex cover C has size ν. Its complement
is independent. If J is the set of nonleaf vertices in that complement,
then at least 2|J| edges lie in the forest induced by C union J, whence
|J| <= ν-1. There are therefore at least n-2ν+1 original leaves outside
C. Remove the possible original head-root leaf. Let L be the number of
remaining leaves; then L >= n-2ν >= n/3.

Group these leaves by their hub in C. Let g <= ν <= n/3 be the number
of nonempty groups and let l_1,...,l_g be their sizes. The g star blocks,
each consisting of one hub and its grouped leaves, are vertex-disjoint.

Each block has at most l_i+2 allowable membership patterns. If the hub is
absent, all its grouped leaves are absent, giving one pattern. If the hub
is present, inward leaves are forced present, omitted leaves forced
absent, and at most one of its outward leaves can be selected. This gives
at most l_i+1 further patterns. Any further constraints only reduce this
upper bound.

The number of allowable subsets of all n tree vertices is consequently
at most

    2^n 2^(-L-g) product_i(l_i+2)
      <= 2^n 2^(-L-g) (2+L/g)^g
      <= 2^n (3/4)^(n/3).

The first inequality is the arithmetic-geometric mean inequality. For
F(L,g)=2^(-L-g)(2+L/g)^g, the logarithmic derivative in L is
-ln(2)+g/(2g+L)<0. Its derivative in g is
ln(1+L/(2g))-L/(2g+L)>0. Thus substitute L=n/3 and g=n/3.
The case g=0 is impossible because L>=n/3>0.

Combining both matching regimes gives the uniform capacity
n 2^n (3/4)^(n/3).

## Covering all sufficiently large odd ties

There are exactly 2^(N-1)=2^n odd label subsets. Removing odd sizes below
m0 leaves

    2^n - sum_(odd j<m0) binom(N,j).

At each remaining generic tie, the hypothesized functional kills the
lower remainder and all outward-twin top germs, but is nonzero on the
maximum. At least one expansion term must therefore have a surviving
germ. The capacity bound and union bound give the displayed inequality.
Only finitely many tie sizes are excluded, so the numerator tends to one
after normalization by 2^n.

## The remaining proof-search target

The analytic issue is now precisely uniform outward-twin separation on
actual functions modulo the FULL lower-dimensional span. A formal score
on tree descriptions, finite-arity certificate, or identity that vanishes
on a few local tree relations does not establish this. The count above
isolates the missing claim without assuming it or weakening its scope.
