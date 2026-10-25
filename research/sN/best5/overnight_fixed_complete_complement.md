# Sparse complement coordinates for the remaining K3 problem

This is an exact change of coordinates in the complete comparison span,
not a restriction on coefficients or preactivation shapes. Let g be
translation invariant, put v(S)=g(1_S), and define

    a_i = v([5] minus {i}),
    c_ij = v([5] minus {i,j}).

The fifteen numbers satisfy the single relation

    sum_(i<j) c_ij = 3 sum_i a_i.

Conversely, every such tuple defines a unique invariant function in the
fourteen-dimensional span through

    g(x) = sum_(i<j)(a_i+a_j-c_ij) max(x_i,x_j) - sum_i a_i x_i.

To see this, write the Boolean quadratic v([5] minus T) as
sum_(i in T) a_i + sum_(i<j in T) b_ij. Its two-point values give
b_ij=c_ij-a_i-a_j. Its value at T=[5] is v(empty)=0, which gives the
displayed relation. Expanding back in 1_S proves the function formula.
Boolean rays determine every braid-linear invariant function, so this
is an identity on all of R^5, not only Boolean inputs.

For any T of size t, the ray formula becomes

    v([5] minus T) = sum_(i<j in T)c_ij - (t-2)sum_(i in T)a_i.

Thus quad values are a_i, triple values are c_ij, pair values are sums of
three c's minus three a's, and singleton values are sums of six c's minus
twice four a's. The generic locality cover for the ordered outside pair
(i,j) is simply that some neuron has c_ij=a_i=0. Both outside orders are
required. The quadruple cover is that some neuron has a_i=0.

The earlier all-four-tie-zero subfamily is precisely a=0; its edge
coordinates c satisfy sum c=0. That subfamily does not exhaust the full
problem. The twelve canonical quad-cover cases impose five selected
zeros among the fifteen a-coordinates across the three neurons, retaining
overlapping zeros and all unbounded c-coordinates.

The accompanying standard-library checker verifies the coordinate inverse
on all fourteen original basis functions, as well as the ray formula on
all32 Boolean subsets. Linearity makes this a complete algebraic check,
not a finite-coefficient experiment. This sparse parameterization is a
possible next solver formulation; no extra search or width claim follows
from it.
