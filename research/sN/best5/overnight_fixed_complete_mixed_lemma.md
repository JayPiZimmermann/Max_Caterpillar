# Complete comparison K2/K3: not all core neurons can cross one chamber

**Status:** independently reviewed mathematical proof. All coefficients
are real and unbounded. This strengthens `overnight_fixed_complete_edge_lemma.md`:
no global four-tie-zero hypothesis is needed.

Let V be the span of the linear functions and all sigma(x_i-x_j), i<j,
on five coordinates. Consider an exact identity

```
max5 = R + sum_(k=1)^K d_k sigma(g_k),  K=2 or3,
```

with R,g_k in V, each g_k translation invariant, and each d_k nonzero.
A common-translation limit reduces any identity in V to this invariant
case without increasing K: nonzero-slope outer terms become shallow and
are absorbed into R. Biases are removed by recession if starting from an
actual network. There is no restriction to rational coefficients.

## Two necessary locality covers

Write v_k(S)=g_k(1_S). Then v_k is a Boolean polynomial of degree at most
two, and v_k(empty)=v_k([5])=0. At every four-label top tie U, at least one
v_k(U) is zero. Otherwise all outer units linearize in a neighborhood of
the tie and the local maximum of four coordinates would be shallow.

At every generic top triple tie T, with the remaining two labels strictly
ordered and U=T union{the higher remaining label}, at least one neuron
satisfies v_k(T)=v_k(U)=0. Indeed the tie cone consists of positive
combinations of1_T and1_U, plus common shifts. A neuron whose restriction
to this cone is a nonzero linear form is nonzero at a generic point of
it. Finitely many such zero lines cannot cover the whole cone. If no
neuron vanishes identically there, choose a generic point where every
preactivation is nonzero; the local max of three coordinates would again
be shallow. This proves the joint-zero cover, with all boundary cases
retained.

The non-shallowness of max3 and max4 follows directly from their varying
normal jump along a coordinate-equality hyperplane: the jump is nonzero
where those two labels are highest and zero where a third label is higher.
A homogeneous shallow function has one constant consolidated jump along
any fixed first-layer hyperplane.

## No chamber with every core preactivation mixed

Suppose all K preactivations take both strict signs in a braid chamber,
ordered pi(1)>...>pi(5). Target and remainder are linear there. Every
interior zero wall needs at least two folded neurons for curvature
cancellation. For K=2 or3, this forces all K nonzero linear forms to share
one hyperplane and hence be proportional on the chamber.

Let S_j be the first j labels. In positive gap coordinates t1,...,t4,

```
g_k = sum_(j=1)^4 t_j v_k(S_j).
```

The four-tie cover gives v_k(S4)=0 for some k, and proportionality makes
it zero for every k. Apply the generic triple cover to(T,U)=(S3,S4).
It gives v_k(S3)=v_k(S4)=0 for some k, so proportionality also makes every
v_k(S3) zero. Thus all forms have shape

```
A_k*t1+B_k*t2,
```

where strict crossing requires A_k and B_k to be nonzero and opposite.
Their common wall meets the relative interiors of both bottom-swap facets
t3=0 and t4=0. Its restriction to either facet is nonzero and changes
sign there. Continuity therefore makes every g_k mixed in the neighboring
chamber. Since K is at most three, all are proportional there as well,
and the two locality covers again kill the last two chain coefficients.

Iterate these adjacent swaps through all permutations of the bottom three
labels, leaving the top two fixed. Put A=S2 and B=[5] minus A. The result is

```
v_k(A union T)=0 for every nonempty T subset B.
```

For |T|=1,2 these are the propagated triple and quadruple zeros; for |T|=3
it is translation invariance v_k([5])=0. The third mixed difference of the
quadratic Boolean function v_k on this three-dimensional cube vanishes.
It therefore also forces v_k(A)=0. This contradicts B_k!=0 above.

This proves the claim. Identically zero forms are not strict crossings and
never create a missing crease. Weak signs and equality cases are retained
in the complementary cases below.

## Consequence for K2: an analytic exclusion

For K=2, one mixed unit alone cannot cancel, and both mixed units have just
been excluded. Hence each individual folded function sigma(g_k) is linear
on every braid chamber. The conforming-function theorem of Grillo,
Hertrich, and Loho excludes max5 from the span of such two-layer functions,
regardless of width; adding the shallow R does not change that conclusion.
Equivalently their Proposition B.2 gives zero fifth Boolean mixed difference
for each conforming fold of a quadratic Boolean function, whereas max5 has
nonzero fifth mixed difference. See
[Theorem5.2 and PropositionB.2, arXiv v2](https://arxiv.org/html/2502.09324v2#S5).

Thus K2 is impossible in the complete comparison span. This supplies a
short mathematical route to the lower bound already established by the
4772-tree certificate. The archived certificate remains unchanged.

## Consequence for K3: the pair-cone model is complete

For K=3, there can be zero or two mixed preactivations in any chamber.
In the two-unit case their output signs are opposite. Absorbing output
magnitudes into g_k makes the chamber-linear preactivations exactly equal
or opposite. The third preactivation has a weak fixed sign on that whole
chamber. This is precisely the finite closed disjunction used by the
pair-cancellation QF_LRA model.

Therefore, for complete-comparison K3, pair cancellation is necessary,
not an extra construction hypothesis. Conversely those whole-cone
conditions, together with exact Boolean-ray output equations, imply a
global identity: the output is linear on each full braid cone and agrees
with max5 on its generators. Continuity covers all boundaries.

Both mixed output-sign counts must be tested. All-positive and all-negative
cores cannot cancel any interior wall, so the same cited conforming theorem
excludes them. A successful rational candidate must still pass the
independent physical global checker. A solver timeout or bare UNSAT verdict
is not an independently checked mathematical infeasibility certificate.

## Audit boundary

The parent and the independent proof agent reviewed the locality covers,
proportionality, facet propagation, weak/strict distinctions, and the final
quadratic third difference. The parent independently verified the cited
conforming theorem and its application. This note is a written mathematical
proof, not a new Lean declaration. It applies to the complete comparison
first-layer span, not arbitrary first hidden layer directions.
