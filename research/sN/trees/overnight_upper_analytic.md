# Analytic routes and failed shortcuts in the overnight upper search

24 October 2026. These arguments do not establish an exponential construction.

## A common apex cannot support a construction

Suppose every second-hidden-layer unit has one fixed apex label `a` and the
form `sigma(g(x_without_a)-x_a)`, where `g` belongs to the first-hidden-layer
span (a linear function plus a sum of functions `sigma(x_i-x_j)`). This permits
arbitrary inner graphs, coefficients, orientations, and cycles away from `a`.
In direction `-e_a`, the positive directional germ of each unit is
`g(x_without_a)-x_a`, while the opposite germ vanishes. Thus its signed
directional derivative belongs to the first-hidden-layer span. The maximum's
corresponding derivative is `max_{i != a} x_i` minus a linear function. For
at least three remaining labels, this cannot lie in that span: the odd part
of a homogeneous one-hidden-layer function is linear, whereas the odd part
of the three-input maximum is not. Extra labels can be identified to reduce
to three inputs. Hence an exact construction in this model must use several
apex labels. A fixed-apex scalar gluing identity cannot suffice.

For the top quotient, the same obstruction follows by the directional
filtration rule: the top class of the smaller simplex remains nonzero, while
the common-apex unit derivatives have only first-hidden-layer complexity.

## Prescribed matching coverage is not a necessary condition

The six-label balanced family contains trees realizing fourteen of the
fifteen perfect matchings; it misses the opposite pairs `(0,3),(1,4),(2,5)`.
The BFS family realizes twelve. Their union realizes all fifteen. These are
exact finite combinatorial observations, recorded in
`overnight_upper_matching_patterns_7.json`.

They do not imply an obstruction. In fact, the already certified seven-input
noncrossing-caterpillar identity uses only noncrossing trees and therefore
omits crossing perfect matchings. Consequently no valid functional can force
every prescribed matching to occur in a canonical tree construction. In a
paired-frequency limit, the distinguished zero-frequency label acting as
the apex can isolate a prescribed matching, but units with other apices must
also be retained. Ignoring those terms would contradict the known identity.

## Group closures preserve exponential size

If a dictionary has at most `poly(N)c^N` descriptions, closing it under the
modular affine group `x -> ax+b` on `Z/NZ` multiplies its size by at most
`N phi(N) <= N^2`. This provides a genuine enlargement of the original cyclic
and reflected orders, while retaining the same exponential base. At seven
inputs, the full BFS closure has 6,216 of the 9,072 apex/tree graphs and
16,584 function orbits under the order-42 group. The existing noncrossing
seven-input witness has 1,428 supported units outside it, so that witness
does not settle this new candidate.

Larger binary linear groups give another valid uniform enlargement.
`GL(k,2)` on `2^k-1` labels and `AGL(k,2)` on `2^k` labels have size
`2^{O(k^2)}`, which is subexponential in the arity and can be absorbed into
an exponential description bound. Restricting an exact construction at the
next such arity by identifying surplus coordinates preserves its width;
the arity is less than twice the desired one. Identification may produce
cycles, repeated edges, or zero edge functions, so the resulting claim is
about the broader network construction rather than the original canonical
tree dictionary.

The small binary-group tests are deliberately not run: exact inventories show
that the seven-input GL closure and eight-input AGL closure of full BFS already
contain every apex/tree graph. All roots and orientations then give the entire
canonical tree dictionary. A positive span result at those arities would not
discriminate the uniform candidate. The modular-affine closure at seven inputs
does omit graphs and remains a meaningful finite test.
