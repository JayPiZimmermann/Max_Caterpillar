# Cycle locality with arbitrary heads and inner coefficients

These are mathematical research results, with exact combinatorial controls.
They are not Lean declarations and do not settle the unrestricted all-tree
bound or the unrestricted exponential construction problem.

## Germ rank

Consider a second-hidden-layer unit

`U(x)=sigma(h(x)+sum_e c_e sigma(x_i-x_j))`,

where `h` is any linear function, coefficients `c_e` may be signed, and the
comparison edges form a subgraph of a cycle on the labels other than one
omitted apex `a`. Edge orientations, edge weights, omitted edges, and linear
edge states may be arbitrary; linear states are absorbed into `h`.

For a label set `T` of size `m`, take the direction with value one on `T`
and zero outside, and restrict its directional germ to perturbations of the
tied coordinates. A comparison with unequal endpoint values has linear or
zero germ. A comparison entirely outside `T` restricts to zero. The only
remaining nonlinear comparisons are the edges of the induced graph on
`T\{a}`. Their span has rank `r`.

If the outer preactivation is positive, its germ is in `L1`; if negative,
its germ vanishes. If it is zero, the germ depends on at most `r+1` linear
forms: the free comparisons and the one resulting head. Hence it belongs
to `L_(r+1)`. This argument does not require convexity: a CPWL function on
at most `r+1` variables is a difference of convex CPWL functions on that
space. A maximum of the `m` tied coordinates has nonzero class modulo
`L_(m-2)`. Thus some unit in any exact expansion must satisfy `r>=m-2`.

The auxiliary term may be any finite first-hidden-layer span, which includes
the paper's `A_N`; its germ is in `L1`. Arbitrary higher-dimensional CPWL
terms cannot be included as free auxiliaries in this statement.

## Uniform obstruction for affine cycles

For every integer `N>=31`, set `T={1,2,4,8,16}`. Its ten positive pair
differences are distinct: the factorization
`2^j(2^(k-j)-1)` uniquely determines `j` and `k`. They are at most 15, so
their positives and negatives are distinct modulo `N` as well.

A cycle on `Z/NZ` in affine order, with one apex removed, has edges of one
difference class `±u`, together with at most one gap edge of difference
`±2u`. Here `gcd(u,N)=1`. At most one edge in either difference class can
have both endpoints in `T`. Consequently every such unit has at most two
free comparisons at this five-label tie. Its nonlinear germ lies in `L3`,
whereas the five-input maximum has simplex dimension four and does not lie
in `L3`.

Therefore this affine-cycle family cannot represent `max_N` for any
`N>=31`, even with arbitrary linear heads, arbitrary signed inner
coefficients, and all edge states. The result includes all sufficiently
large prime arities, so prime padding cannot give a uniform construction
from this family. It says nothing against affine BFS trees or against
denser graphs.

## Exponential lower bound for arbitrary cycle orders

Now allow every cycle order, rather than only affine orders. Put `L=N-1`
and choose `3<=m<=N-2`. A proper induced subgraph of the cycle is a forest.
If the omitted apex lies in `T`, the free graph has `m-1` vertices, and
`r>=m-2` forces it to be connected: one circular arc. There are exactly
`L` such choices of `T` for the fixed unit.

If the apex lies outside `T`, the induced graph has `m` vertices and at
most two connected components. There are `L` one-arc subsets. Two-arc
subsets are counted by choosing positive lengths for two selected arcs
and two complementary gaps, choosing a circular start, and dividing by
two for the choice of first selected arc. Their number is

`L (m-1) (L-m-1) / 2`.

Deleting comparison edges can only lower rank. Thus a single unit can
contribute to at most

`B(N,m)=2(N-1)+(N-1)(m-1)(N-m-2)/2`

of the `m`-label top ties. For every exact finite expansion using `K` such
units and a first-hidden-layer auxiliary span,

`|K| >= binom(N,m) / B(N,m)`.

Taking `m=floor(N/2)` gives `|K|=Omega(2^N/N^(7/2))`. This is a lower
bound for cycle-supported units with arbitrary heads and signed inner
coefficients, not for unrestricted trees: a high-degree star can have
exponentially many connected induced subsets.

`overnight_upper_cycle_locality.py` checks the Sidon arithmetic and all
affine cycles at four arities, and independently enumerates circular
subsets to verify every fixed-size capacity formula for `5<=N<=14`.
