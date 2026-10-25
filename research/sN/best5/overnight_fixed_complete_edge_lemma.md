# Four-tie-zero K3: three-way crossing cannot occur

**Status:** mathematical proof, independently reviewed. This is a statement
about the complete comparison span under an explicit four-tie-zero
hypothesis. It does not assert that every K3 representation has that
hypothesis or establish a new unrestricted second-width lower bound.

Let `V=span{x_i,sigma(x_i-x_j):i<j}` for five coordinates. Suppose

```
max5 = R + sum_(k=1)^3 d_k sigma(g_k),
```

where R,g_k belong to V, the g_k are translation invariant, and all
`d_k!=0`. Normalize output magnitudes into the preactivations if desired.
Assume every g_k vanishes on every Boolean ray1_U with |U|=4. As usual,
one may discard zero-output or identically zero neurons; the existing
complete-comparison K2 exclusion then rules out such a smaller exact
representation.

## Exact edge coordinates and their cover

Every such g_k has unique edge coefficients b_ke, for the ten unordered
pairs e={i,j}, satisfying

```
sum_e b_ke=0,
g_k(x) = -sum_e b_ke max(x_i,x_j),
g_k(1_S) = sum_(e subset complement(S)) b_ke.                (1)
```

For completeness, write its Boolean ray function as
`v(S)=sum_(i in S)c_i+sum_(e subset S)q_e`. The full-set and four-set
zeros imply `c_i=-sum_(e incident i)q_e` and `sum_e q_e=0`.
Then `v(S)=sum_(e subset complement(S))q_e`. Comparison-span functions
are determined by all their Boolean rays, so q gives(1).

A generic top triple tie with top set T has complement edge e. If all
three b_ke were nonzero, every outer ReLU would have fixed sign in a
neighborhood of a generic point of that tie, so the local output germ
would be shallow. The three-way maximum germ is not shallow. Hence

```
for every edge e, at least one of b_1e,b_2e,b_3e is zero.     (2)
```

Equivalently this follows from the exact generic-triple locality equations
already used in the complete K2 certificate. No sign or size cutoff is
used in(2); additional zero entries are allowed.

## Claim

There is no braid chamber on which all three g_k take both strict signs.
Therefore every interior outer wall in a braid chamber is cancelled by
exactly a positive/negative pair; the third preactivation has a weak fixed
sign on that whole chamber. In this subfamily, pairwise cancellation is
a necessary condition, not merely a constructive restriction.

## Proof

Fix an order pi and write the chamber as positive gaps t1,t2,t3,t4 plus
a common coordinate shift. Its extreme directions are1_{S_j}, where
`S_j={pi(1),...,pi(j)}`. Thus

```
g_k(x)=sum_(j=1)^4 t_j g_k(1_{S_j}).                        (3)
```

Suppose all three preactivations cross the chamber interior. The target
and R are linear there. At every interior zero hyperplane the signed
normal derivatives of the folded terms must cancel. A wall needs at least
two neurons with nonzero output coefficients. With only three crossing
neurons, all three must have the same zero hyperplane. Their nonzero linear
forms are therefore proportional. This argument does not assume pairwise
cancellation in advance.

By(2), at least one g_k(1_{S_3}) is zero; proportionality forces all three
to be zero. The four-tie hypothesis gives g_k(1_{S_4})=0 as well. Hence
all three forms have shape

```
g_k(x)=A_k*t1+B_k*t2,
A_k=g_k(1_{S_1}), B_k=g_k(1_{S_2}).                         (4)
```

Strict crossing forces A_k and B_k to be nonzero and opposite in sign.
Their common zero wall therefore meets the relative interior of each
facet t3=0 and t4=0: choose positive t1,t2 with A_k*t1+B_k*t2=0 and keep
the other unconstrained gap positive.

Across either facet the restriction of each g_k is nonzero and changes
sign near that intersection point. Continuity supplies both signs in the
adjacent chamber. Consequently all three neurons also cross that chamber,
so they are again proportional and(2) again forces their new |S|=3 ray
values to vanish. Their |S|=4 values remain zero by hypothesis.

Swapping positions3 and4 or positions4 and5 generates every ordering of
the bottom three labels, with the first two fixed. The preceding argument
iterates through these six chambers. The values A_k and B_k stay unchanged
because S_1,S_2 stay unchanged. Every pair among the bottom three appears
as the complement of S_3 in one of those chambers. Formula(1) therefore
forces all three edge coefficients of that bottom triangle to be zero,
for every k. But again by(1), their sum is exactly B_k. This contradicts
B_k!=0 in(4).

The argument handles both mixed output-sign patterns. A preactivation
identically zero on a chamber is not a strict crossing and introduces no
missed wall. If only two neurons cross, their walls must coincide and their
normalized preactivations are equal or opposite on the entire chamber;
if only one crossed, its crease could not cancel. All weak and zero
boundaries are therefore covered by the stated pairwise cone condition.

## Remainder and the finite search domain

Since the core terms vanish on four-set rays, R has value one on all those
rays and common-shift slope one. Thus

```
R=sum_e r_e max(x_i,x_j),  sum_e r_e=1.
```

Evaluating at the complementary triple gives
`r_e=sum_k d_k sigma(b_ke)`. The remaining Boolean-ray equations become

```
sum_(e subset T) r_e = sum_k d_k sigma(sum_(e subset T)b_ke)
```

for every three- and four-vertex set T. These are exact identities. They
remove the remainder variables from the synthesis model.

Assign each edge to one of its zero entries in(2). All3^10 assignments
form a closed cover, including multiple-zero boundaries. There are142
orbits under S5 vertex permutations and S3 neuron permutations. An
independent standard-library checker expands those orbits and verifies
disjoint coverage of all59,049 assignments. The output-sign cases must
still distinguish the minority output color; quotienting by color
permutations does not discard those choices.

The first global reduced pair-cone solve with signs(+,+,-) was reported
UNSAT in55.9 seconds. That is a solver diagnostic, not an independently
checked infeasibility certificate. The lemma justifies the necessity of
its cone restriction within this subfamily; it does not certify that
solver verdict. The known four-core `(10,6)` control satisfies the edge
model and passes the independent global checker.
