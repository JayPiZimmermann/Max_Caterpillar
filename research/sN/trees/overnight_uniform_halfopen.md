# Half-open lattice lift: actual descent, but the first torsion gates fail

25 October 2026. The lattice lift below is a linear operation on actual
rational kernels. Its complete circuit descent is proved and independently
reviewed. Two specific scalar torsion coefficients fail exactly at five
labels. Neither the lift nor those failures settle outward-twin separation.

## A boundary-consistent lattice operation

Let V be the frequency-form space, with lattice L=Z^N/Z(1,...,1). Fix one
generic frequency xi, and polarize every arrangement form alpha so that
alpha(xi)>0. All resulting rays lie in one open halfspace. For a polarized
basis B=(beta_1,...,beta_r), let C_B be its positive cone. In lattice-normalized
volume,

    Laplace(1_(C_B)) = |det B| / product_i beta_i.

Thus the inverse cone representative of a basis fraction is its polarized
cone indicator divided by |det B|, with the product of polarization signs.
Rational identities of basis fractions give identities of these cone
indicators almost everywhere. This is the cone/Laplace interpretation of
the full basis-fraction circuit presentation, not merely the local Fay
identity. See [Brion–Vergne, Sections 5 and 7](https://arxiv.org/html/math/9903178).

Choose one common generic primal vector eta, avoiding the spans of all
proper cone faces in the finite arrangement. Replace an indicator at a
lattice point m by its value at m+epsilon eta for sufficiently small
positive epsilon. Every point then avoids every relevant boundary, so
every almost-everywhere cone identity becomes a pointwise lattice identity.
The choice is common to all bases; choosing independent boundary conventions
for different cones would invalidate this argument.

Because the face hyperplanes are rational, epsilon can be chosen uniformly
over all lattice points for this finite arrangement. A nonzero integral
normal value at a lattice point has a uniform positive lower bound, while
its change under epsilon eta is uniformly bounded over the finitely many
face normals. The resulting lattice series converge in a common polarized
region and give identities of rational functions after continuation.

Consequently the half-open lattice generating series defines a linear map
on S_Delta. It respects ALL circuit relations, including those exchanging
apex roles. Composing it with the marked embedding R -> (omega_j R)_j is
therefore a genuine operation on the original function's generic Fourier
kernel, and it kills the full lower-dimensional span generically.

## Explicit basis formula and the nonunimodular caveat

For a unimodular unpolarized basis B, put c=B^(-1) eta. Then its lift is

    H_eta(1/product_i beta_i)
       = z^(sum_(i:c_i<0) beta_i) / product_i(1-z^beta_i).

This unpolarized formula equals the polarized one as a rational function.
Reversing a ray replaces its boundary convention by the complementary one;
the denominator identity 1-z^(-beta)=-z^(-beta)(1-z^beta) gives exactly the
required sign. Thus computation need not repeatedly polarize bases.

Canonical bases a,q_e+b_e epsilon_e a are unimodular, so their fundamental
parallelepiped has one lattice point and the numerator is one monomial.
For an arbitrary circuit-intermediate basis, however, the correct formula
has the full sum over lattice points in its eta-half-open fundamental
parallelepiped, divided by |det B|. Applying the single-monomial formula to
a nonunimodular basis would destroy the descent proof.

The simplest boundary control is the rank-two circuit with eta=(1,10):

    1/[(1-X)(1-Y)]
      = X/[(1-X)(1-XY)] + 1/[(1-Y)(1-XY)].

Its numerators satisfy 1-XY=X(1-Y)+(1-X). The factor X is the necessary
half-open correction; closed cones would count their common ray twice.

## Exact first torsion gate

Use N=5, mark j=0, and the basis of V given by omega_1,...,omega_4. Set

    eta=(1,10,100,1000),
    z_0=(1+s)^(-40),
    (z_1,z_2,z_3,z_4)=(-(1+s),-(1+s)^3,-(1+s)^9,-(1+s)^27).

The product of all five z_i is 1, so this is a legitimate curve in the
character torus of L. Its perturbation is generic for the tested arrangement.
Take the coefficient of s^0 in H_eta(omega_0 R). This is an actual linear
functional, not a score on a tree presentation.

For max_5 the value is 1/16. For the unaveraged full S_5 orbit of the outward
star with apex0, center2, and edges (1,2),(3,2),(4,2), its value is

    -57047/3360.

Thus this scalar torsion coefficient does not annihilate outward twins.
The producer checked all ten rooted oriented star orbits; the root-slide
equivalent columns agree exactly. The calculation took about one second.

The independent standard-library checker uses the closed star expression
R=-a/product_l[l(l+a)] and the twenty ordered apex/center choices, with six
leaf permutations each. It obtains the same 97 surviving basis terms. It
uses Cramer's rule and one polynomial quotient after removing the powers of
t-1, instead of the producer's rooted-cut inventory, Gaussian elimination,
and product of Laurent inverse series. The exact values and the elementary
rank-two circuit both pass.

## The single label-covariant correction also fails

Average the COMMON vector eta over all permutations of the five-label
representative (0,1,10,100,1000), then quotient by the diagonal. In the
chosen basis these vectors are (p_1-p_0,...,p_4-p_0). Keep the marked
coordinate and the torsion curve fixed. Every summand separately respects
all circuit relations, so the average does too.

The exact averaged maximum value is 1/80, while the same full outward-star
orbit has value

    -368789/151200.

The averaging producer took about 4.6 seconds. A second calculation uses
the initial rooted-cut/Gaussian/product-Laurent route rather than the
averaging producer's closed-star/Cramer/single-quotient route and reproduces
both fractions. This second route is independent of the averaging producer,
but intentionally reuses the initial unsymmetrized-gate implementation.

For the target, the averaged value also follows directly: each reference
rank occurs 4! times, and its numerator sign is (-1)^rank. Hence its
120-term mean is [1-1+1-1+1]/[5*2^4]=1/80.

## Commands, scope, and next residual

Run the initial gate with the research Python environment:

    research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/overnight_uniform_halfopen_gate.py

The independent first check and averaged gate use the standard library:

    python3 research/sN/trees/overnight_uniform_halfopen_verify.py
    python3 research/sN/trees/overnight_uniform_halfopen_average.py

Recheck the average through the alternate arithmetic route:

    research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/overnight_uniform_halfopen_average_check.py

The failures concern only the two declared constant-coefficient functionals.
They do not refute separation in the full torus-valued image. Blindly adding
more Laurent coefficients would merely create another finite fitting problem.
The useful new result is the boundary-consistent descent construction. A
future torsion or graph interpretation must use its actual half-open boundary
weights and prove outward-twin vanishing uniformly, including every apex.
