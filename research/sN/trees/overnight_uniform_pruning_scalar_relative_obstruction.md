# Why a scalar local separator cannot be tensorized by retaining outside variables

25 October 2026. This is a structural obstruction to an operator, not a
counterexample to the unrestricted all-tree lower bound.

Let `Lambda` be a linear functional on five-label top germs, normalized by
`Lambda(max_5)=1`, which annihilates `L_3` and every canonical star unit.
Choose a canonical four-vertex path unit `U_0` with
`c=Lambda(U_0)!=0`. Such a unit exists because the signed caterpillar identity
expresses the maximum's top class using path and star units.

There is also an explicit example for the independently checked signed-root
functional from `overnight_uniform_pruning_signed5_check.*`:

```
U_0(x) = sigma(x_1-x_0
              +sigma(x_2-x_1)+sigma(x_3-x_1)+sigma(x_4-x_2)).
```

For its symmetrized normalization, `c=60/5!=1/2`: the certificate evaluates
the unaveraged orbit of this unit to60 and the maximum kernel to1.

Fix a nonapex core vertex `h`, for example `h=1`. Add `k>=1` new labels
`y_1,...,y_k`, always with the explicit hinge orientation

```
sigma(y_l-x_h).
```

If `g_0` is the preactivation of `U_0`, define the larger canonical unit

```
U(x,y)=sigma(g_0(x)+sum_(l=1)^k sigma(y_l-x_h)).         (1)
```

Its inner tree consists of the core path plus leaves at a single core
vertex. Its matching number is exactly two, for every `k`. The old perfect
matching gives two edges. A matching using a new leaf can use only one such
edge; it then removes `h` and leaves three old core vertices, on which at
most one additional matching edge is possible.

## The complete scalar field agrees with the maximum's field

Tie the five core coordinates at their common value `t`, retaining all the
outside variables `y`. On the open set where no `y_l=t`, take the local germ
in the five core coordinates and apply `Lambda`. Call this scalar field
`S_U(t,y)`.

If every `y_l<t`, all the added hinges are inactive near the tie. The base
preactivation is zero, and the local germ is exactly `U_0`, so `S_U=c`.

If at least one `y_l>t`, the base preactivation in (1) is strictly positive.
The outer ReLU is locally linear. Its germ is a linear function plus a sum
of individual functions `sigma(x_i-x_j)`, hence lies in `L_1` and has
`Lambda` value zero. Therefore

```
S_U(t,y) = c * 1_{t>max_l y_l}.                        (2)
```

For the larger maximum itself, the identical argument gives

```
S_(max_(k+5))(t,y) = 1_{t>max_l y_l}.                  (3)
```

Consequently the two scalar fields are proportional on every open external
chamber. The values on the equality walls are immaterial for the integral
below. More generally, **any linear postprocessing that factors only through
this scalar field gives proportional outputs**. Retaining the outside
variables after taking a scalar five-label response does not retain enough
information to distinguish this bounded-matching unit from the target.

## Exact integration convention

For each fixed `y`, use the antiderivative that vanishes when `t` is below
all the outside coordinates:

```
T(U)(t,y) = integral_(s=-infinity)^t S_U(s,y) ds
         = c * sigma(t-max_l y_l)
         = c * [max(t,y_1,...,y_k)-max(y_1,...,y_k)].   (4)
```

The integral converges because its integrand is zero for all sufficiently
negative `s`. This convention fixes the otherwise arbitrary function of
`y` that could be added to the antiderivative.

The second maximum in (4) is supported on the proper simplex face spanned
by the outside labels and belongs to `L_(k-1)`. Thus the resulting top class
is `c` times the nonzero `(k+1)`-label maximum class. Exactly the same
operator sends the target to that maximum class with coefficient one.

Taking `k` arbitrarily large shows that this scalar local procedure cannot
consume two matching edges at every step, or preserve the class of trees
with matching number at most two. A viable relative five-to-one operator
must retain attachment/head information before collapsing the local germ
to one scalar. This is the precise residual for a marked-kernel or
attachment-state tensorization.

## The same obstruction holds at every fixed odd block size

Replace five by `m=2q+1`. Suppose the scalar block functional detects
`max_m` and vanishes on all non-perfect-matchable canonical inner trees.
Some perfectly matchable core unit has nonzero response by the known
caterpillar expansion. Attach arbitrarily many hinges `sigma(y_l-x_h)`
to one core vertex. The resulting tree still has matching number exactly
`q`: using an added leaf leaves `2q-1` old vertices, on which at most
`q-1` matching edges fit. The entire scalar local-germ field is again the
same nonzero multiple of the maximum's field. Therefore the obstruction
applies equally to a scalar relative seven-to-one construction using the
exact seven-label matching separator, and to any larger fixed odd block.
