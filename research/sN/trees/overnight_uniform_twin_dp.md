# Outward-twin counting is bounded by a Fibonacci sum

25 October 2026. Uniform mathematical counting proof, independently reviewed
by the parent. The actual-function separator assumption remains open.

Assume that, for every odd m>=m0 for some fixed m0>=5, a linear functional
modulo L_(m-2) is nonzero on max_m and annihilates every canonical tree unit
with two nonroot outward leaves at one hub. Thus both functions at those
leaves are sigma(x_leaf-x_hub). Every root, apex, and other orientation is
included. This hypothesis is strictly weaker than uniform separation of
all trees without a perfect matching.

Under that hypothesis every exact expansion of max_N by K canonical tree
face functions and the existing shallow auxiliary span satisfies, for
N>=m0,

    |K| >= [2^(N-1) - sum_(odd j<m0) binom(N,j)] / [F_(N+2)-2],

where F_1=F_2=1. In particular the conditional exponential rate is 2/phi,
approximately 1.236, with no polynomial loss. This is the same rate as
the stronger perfect-matching separator hypothesis, with a constant loss
in the denominator. No unrestricted exponential lower bound is claimed.

## Canonical germs and the original rooting

Root the original tree T at its canonical head r. At a generic top tie,
the existing negative superincreasing-base and head-flow argument forces
the apex to remain tied and the other tied vertices S to induce a connected
tree containing only hinge edges internally. The transported head v is the
vertex of S nearest to r. Thus S is contained in the original descendant
subtree T_v, and it is ancestor-closed there.

Every excluded child subtree below a selected vertex in T_v contains no
original head. Summing its balanced outside coefficients leaves only the
contribution of its boundary edge. This gives the following necessary rules
when a parent is selected:

* An inward hinge sigma(x_parent-x_child) forces its child to be selected.
  If the child were outside, its negative base value activates the hinge,
  leaving total coefficient -1 in that excluded component.
* An outward hinge sigma(x_child-x_parent) permits either membership state.
* An omitted edge forces its child to be absent, because an internal omitted
  edge would lose the required hinge rank.
* Either linear edge state makes this selected parent impossible: an
  internal linear edge loses rank, while an external linear edge gives a
  nonzero component sum, of either sign.

These are only necessary conditions. The frozen coefficients inside an
excluded component can impose further restrictions, which are ignored.
The branch from v toward the original head is also ignored; this only
increases the capacity. The transported head is exactly v, so every child
which is a singleton selected subtree is a nonroot retained leaf. At most
one outward child of that kind may occur at a selected parent.

## The two-state recurrence

Let A_v count rooted selected subsets of T_v satisfying precisely the
necessary rules above and the prohibition on two outward singleton children.
Let b_v be 1 if the singleton subset {v} is allowed and 0 otherwise.

If v has a linear child edge, then A_v=b_v=0. Otherwise let I_v and O_v
be its inward-hinge and outward-hinge children. Omitted children contribute
no choices. Then b_v=1 exactly when I_v is empty, and

    A_v = (product_(c in I_v) A_c)
          [product_(c in O_v)(1+A_c-b_c)
           + sum_(i in O_v) b_i product_(c in O_v, c!=i)(1+A_c-b_c)].

For an outward child, the normal state is absent or selected nonsingleton,
giving 1+A_c-b_c possibilities. There may also be exactly one exceptional
selected singleton child, giving the displayed sum. These are disjoint
possibilities, so the recurrence is exact for this necessary-set class.

## Matching domination

Let M_v be the number of matchings of the ORIGINAL descendant tree T_v,
including its empty matching. Let M_v^- count matchings after deleting v.
The strengthened induction is

    A_v <= M_v - (1-b_v).

For a leaf both sides equal 1. At any vertex the matching recurrence is

    M_v = product_c M_c + sum_i M_i^- product_(c!=i) M_c.

For an outward child, induction gives 1+A_c-b_c <= M_c. Each inward factor
A_c is also at most M_c. Omitted children can be inserted as harmless
factors M_c>=1. Thus the all-normal term in A_v is bounded by the first
matching term. Each outward singleton term is bounded by its corresponding
root-child matching term because b_i<=1<=M_i^-.

If b_v=0 because there is an inward child i, that root-child matching term
was not used by any outward singleton term. It has integer value at least
one and supplies the strengthened subtraction. If instead a linear child
exists, A_v=b_v=0 and M_v>=1 proves the same inequality immediately. This
completes the induction for every edge orientation and every face state.

## Sum over transported heads

A forest on s vertices has at most F_(s+1) matchings, by the usual leaf
recurrence M(T)=M(T-leaf)+M(T-{leaf,neighbor}). Choose a postorder numbering
v_1,...,v_n of T, where n=N-1. Each descendant subtree T_(v_i) has at most
i vertices. Consequently one original unit serves at most

    sum_v A_v <= sum_(i=1)^n F_(i+1) = F_(n+3)-2 = F_(N+2)-2

tied label sets with surviving outward-twin-free top germs. The apex is
fixed and adds no choice. No division by the number of transported heads
is needed: each connected S has a unique vertex nearest to the original
head.

There are exactly 2^(N-1) odd subsets of all N labels. Removing the odd
sizes below m0 gives the numerator in the theorem. At each remaining tie,
the assumed functional must detect at least one term in the expansion.
The capacity bound proves the conditional lower bound by double counting.

## Reproducible controls and residual

Run:

    python3 research/sN/trees/overnight_uniform_twin_dp.py

The standard-library checker enumerates every rooted tree shape through six
vertices and all five edge states. It compares the recurrence with direct
subset enumeration at every vertex and verifies the strengthened matching
bound and the postorder Fibonacci sum. Through five vertices it separately
freezes every tie subset at the declared negative superincreasing base,
checks coefficient balance, connected hinge rank, canonical transported
head, and absence of outward twins, then verifies membership in the counted
necessary-set class. This last check uses the actual canonical unit formula,
not merely the recurrence rules.

The controls do not construct the uniform separator. That is the entire
remaining analytic hypothesis. A score on tree presentations, including
the symmetric graph class in overnight_uniform_symmetric_complex.md,
cannot substitute for a linear functional on actual functions modulo the
full lower-dimensional span.
