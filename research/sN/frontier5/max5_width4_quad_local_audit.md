# Independent audit of local four-way-tie carriers

## Verdict and scope

**PASS.** In a finite homogeneous shallow free-core representation of
Max5, one normalized positive core can be the unique vanishing core at
at most three of the five points `q_i=-e_i`.

If it uniquely carries three specified points, its nonzero coordinate-
difference ridge graph must be exactly a triangle on those three labels
plus the edge on the remaining two labels. The normalized ridge
coefficients on the triangle are equal, and the complementary edge has
the opposite coefficient; their magnitudes are one.

The proposed shallow function realizes the required comparator germs at
three points. It therefore refutes an attempted improvement to at most
two based only on those local germs and root-ridge compatibility. It is
not a Max5 representation, and it does not itself establish that another
core is nonzero at those three points.

## 1. Why the induced root graph is a signed perfect matching

Suppose a free core g is the unique vanishing core at q_i. All other
outer ReLUs are active or inactive on a neighborhood and can be absorbed
into the local shallow remainder. On the four coordinates other than i,
the target germ is Max4. The independently audited one-core Max4 theorem
therefore forces the unique vanishing core to have positive output
coefficient. Absorb that coefficient into g.

Its local homogeneous restriction is the difference of complementary
pair maxima. In a consolidated expansion using coordinate differences
with either chosen orientation, the two relevant root ridge coefficients
are +1 and -1; all other root ridge coefficients on those four labels
are zero.

For a global root hyperplane `x_j=x_k`, incidence with q_i is equivalent
to i not belonging to {j,k}. Thus the induced graph obtained by deleting
vertex i is exactly that signed perfect matching. Its edge coefficients
are the global consolidated coefficients of g, because a shallow ridge
coefficient is constant along its entire hyperplane.

Nonroot terms do not invalidate this argument. Terms whose hyperplanes
miss q_i are locally affine. A nonroot hyperplane through q_i restricts
to a nonroot hyperplane on the four-coordinate slice and must have zero
consolidated coefficient in the forced comparator germ. Coincident
hyperplanes must be consolidated before this statement is used.

## 2. Four uniquely carried contacts are impossible

Suppose g uniquely carried q_i for every i in a four-element label set
A, and let v be the remaining label. Let d be the degree of v in the
global nonzero-root graph, ignoring edge signs, and let epsilon_i record
whether vi is an edge. The perfect-matching condition after deleting i
gives

```
d-epsilon_i=1  for every i in A.
```

All four indicators are therefore equal to one binary value epsilon.
There are no other possible neighbors of v, so d=4*epsilon. Substitution
gives `3*epsilon=1`, impossible for epsilon in {0,1}. Carrying five
contacts would in particular carry four, so it is also excluded.

## 3. The exact graph when three contacts are carried

Relabel the carried contacts as A={1,2,3} and the other labels as {4,5}.
For vertex 4, deleting any i in A leaves matching degree one. All three
edge indicators from 4 to A are consequently equal to epsilon_4. With
delta the indicator of edge 45,

```
degree(4)=3*epsilon_4+delta,
2*epsilon_4+delta=1.
```

The only binary solution is epsilon_4=0 and delta=1. The same argument
for vertex 5 excludes every edge from 5 to A. Deleting vertex 2 now
forces edge 13, deleting 3 forces edge 12, and deleting 1 forces edge
23. These account for every possible edge, yielding exactly K3 plus K2.

Each induced matching pairs one triangle edge with edge 45. Their
coefficients must be +1 and -1, so the common coefficient of edge 45
forces all three triangle coefficients to be its negative. This proves
the claimed sign compatibility as well as the unsigned graph shape.

## 4. The explicit three-contact shallow germ construction

Let

```
m=(x1+x2+x3)/3,
range3=max(x1,x2,x3)-min(x1,x2,x3),
g=range3+m-sum_{j=1}^3 ReLU(m-xj)-max(x4,x5).
```

This g is homogeneous shallow because

```
range3=(|x1-x2|+|x1-x3|+|x2-x3|)/2,
```

and every remaining term is affine or a ReLU of a linear form, except
the pair maximum which is also shallow. It is translation invariant:
range3 and each m-xj are invariant, while m and max(x4,x5) acquire the
same shift and cancel.

Fix i in {1,2,3}. At q_i, coordinate i is the unique minimum among
the triangle coordinates. Moreover `m-xi=2/3`, and each other m-xj
equals -1/3. These signs persist whenever

```
||x-q_i||_infinity < 1/6.
```

On that neighborhood precisely the i term in the displayed ReLU sum
is active. Let j,k be the other two triangle labels. Then

```
range3=max(xj,xk)-xi,
m-sum ReLU(m-xj)=xi,
g=max(xj,xk)-max(x4,x5).
```

Thus g has exactly the required positive comparator germ near all three
q_i, with the triangle roots contributing +1 and root 45 contributing
-1.

The nonroot hyperplanes m=xj avoid each of q1,q2,q3, so they change
the local affine pieces without creating extra local ridges there.
This is precisely the mechanism absent from a root-only argument.

For clarity, g(q4)=g(q5)=0 as well. Its germs at those points are not
the asserted four-input pair comparators. Another core would need to
vanish there in a full identity. Neither that compatibility nor a full
Max5 identity follows from this local example.

Its linear odd part is

```
g(x)-g(-x)=(2/3)*(x1+x2+x3)-x4-x5.
```

This follows because range3 is even and the three forms m-xj sum to
zero. The construction therefore also retains a simple exact odd form;
no numerical approximation is used.

## Evidence boundary

All statements above were checked symbolically from the proposed
formulas and graph constraints. No numerical search, solver exclusion,
new full-network lower bound, or Lean verification is claimed.
