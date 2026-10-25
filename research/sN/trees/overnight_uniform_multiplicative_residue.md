# Principal parity residue fails for outward stars at every odd arity

25 October 2026. Uniform exact obstruction to one specific scalar functional
of the new faithful multiplicative kernel. This does not refute an
outward-twin separator obtained by another operation.

Put N=2k+1 with k>=2. On the torus product_i z_i=1, take the principal parity
curve

    z_0=t^(-2k),       z_i=-t for every i!=0.

Consider Res_(t=1) G(t) dt/t. For the maximum its value is

    1/(2k*2^(2k)),

which is nonzero. The curve can lie identically in poles of other canonical
units, so it is not automatically a scalar functional on the full dictionary.
However, every outward-star term below restricts to an ordinary rational
function of t with only finite-order poles. Thus these terms are a mandatory
control for any proposed regularization agreeing with ordinary residues
where restriction is already defined.

Take the canonical outward star, with every leaf function sigma(x_leaf-x_hub),
and sum over every label permutation without dividing by N!. Use the exact
multiplicative kernel from overnight_uniform_multiplicative.md. All apex
placements are retained in the following calculation.

If its apex is label 0, the numerator has a zero of order 2k-3 and every
edge denominator is nonzero at t=1. Its residue is therefore zero.

If its apex is not 0 and its center is 0, the kernel is

    -t^(2k) / [(1-t)^(2k-1)(1+t)^(2k+1)].

Its logarithmic residue is

    A_k = 2^(1-4k) (-1)^(k-1) binom(2k-1,k-1).

If neither apex nor center is 0, exactly one leaf has label 0, and the kernel
is

    -t^(4k-2) / [(1-t)^(2k-2)(1+t)^(2k-1)
                 (1-t^(2k))(1+t^(2k-1))].

Let

    P_k(v) = sum_(j=0)^(k-1) binom(2k,2j+1) v^j,
    Q_k(v) = sum_(j=0)^(k-1) binom(2k-1,2j) v^j.

The substitution u=(t-1)/(t+1) gives its logarithmic residue as

    B_k = 2^(2-4k) [v^(k-1)] (1-v)^(4k-3)/[P_k(v)Q_k(v)].

Both residues have the same nonzero sign (-1)^(k-1). For A_k this is explicit.
For B_k, all roots of P_k and Q_k are strictly negative. To see this, write
u=i tan(theta): the difference (1+u)^(2k)-(1-u)^(2k) yields the roots of P_k,
and the sum (1+u)^(2k-1)+(1-u)^(2k-1) yields those of Q_k. Their k-1 roots are

    P_k: -tan^2(j*pi/(2k)),             j=1,...,k-1,
    Q_k: -tan^2((2j+1)*pi/(4k-2)),      j=0,...,k-2.

They are distinct and account for the full degrees. Since P_k(0)=2k and
Q_k(0)=1, the power-series coefficients of 1/[P_k(v)Q_k(v)] alternate with
strictly positive magnitudes. The numerator (1-v)^(4k-3) has the same
alternating sign pattern. Every term contributing to its coefficient of
degree k-1 therefore has sign (-1)^(k-1), and at least one is nonzero.

There are 2k choices of a nonmarked apex, one marked-center choice, and
2k-1 other-center choices. Every apex/center choice has (2k-1)! leaf
permutations. Hence the full orbit's residue is exactly

    (2k)! [A_k+(2k-1)B_k] != 0.

At N=5 it equals -99/32, while the maximum residue is 1/64. Thus even a
regularization handling the other identically singular units cannot make
this ordinary principal parity residue annihilate all outward twins.

The companion checker computes exact coefficients through N=25. At N=5,7,9
it independently differentiates the two rational functions after removing
their poles and compares the results with the transformed coefficient
formula. These are controls of the uniform sign proof, not a sampled
substitute for it.

    research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/overnight_uniform_multiplicative_residue.py

This closes the first principal parity residue. No higher jet alphabet is
being proposed as a consequence. The live problem is a different structural
functional on the faithful all-apex multiplicative kernel.
