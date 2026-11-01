# Coordinate-curvature moments: a rejected shortcut

25 October 2026. This bounded exact instrument does not prove a lower bound.

For a unit `U` and a coordinate `j`, take the `q`th moment of its univariate
second derivative in `x_j`, then take the Boolean mixed difference in every
other coordinate, and finally sum over `j`. These second derivatives are
finite atomic measures because each univariate restriction is convex CPWL.
All atom locations and slope jumps are evaluated as exact rational numbers.
For `max_N` at odd `N`, the resulting value is `-N` for every positive `q`.

There is a tempting perfect-matching argument at `N=2q+1` when `j` is the
unit's actual omitted apex. Its moment is
`(x_root + sum_edges sigma(x_u-x_v))^q`. The full mixed difference on the
`2q` remaining vertices can survive only if `q` selected edge factors cover
all vertices, which requires a perfect matching. A head factor uses only one
vertex and cannot supply the missing coverage.

The other coordinate choices invalidate the proposed symmetric functional.
For all roots and orientations of the four-vertex star, the `q=2` values are
`-9/2,-4,-7/3,-1/2,-1/3,1/4,1`, although the star has no perfect matching.
The maximum's value is `-5`. Orders one, three, and four likewise have nonzero
star values. In addition, no annihilation of the full lower-dimensional span
`L_(N-2)` has been proved for this Boolean-moment functional. The valid
actual-apex coverage observation does not supply either missing bridge.

`overnight_lower_moment.py` reproduces all 32 root/orientation cases and saves
their separate coordinate contributions in `overnight_lower_moment.json`.
