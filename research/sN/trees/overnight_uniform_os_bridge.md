# A complete presentation for a possible separator map

25 October 2026. Exact algebraic reduction, not an all-tree separator.
This is a fresh structural route after the failed tree-score and fixed-block
flag constructions. It retains the marked frequency and includes every apex.

## Elementary embedding into basis fractions

Let N>=3, d=N-2, and let a be the apex frequency. For a canonical unit write

    R = (-a)^(d-2) product_e 1/[q_e(q_e+epsilon_e a)],

where epsilon_e is +1 or -1 and q_e is the cut frequency away from its root.
The d+1 forms a,q_1,...,q_d form a basis on the N-1 dimensional frequency
space. The identity

    1/[q(q+epsilon a)] = (epsilon/a)[1/q-1/(q+epsilon a)]

gives

    aR = (-1)^(d-2)(product_e epsilon_e)/a
         * sum_b (-1)^|b| product_e 1/(q_e+b_e epsilon_e a).

For an individual cut coordinate q_j, first cancel its denominator:

    q_j R = (-1)^(d-2)(product_(e!=j) epsilon_e)
             /[a(q_j+epsilon_j a)]
             * sum_(b on e!=j) (-1)^|b|
                 product_(e!=j) 1/(q_e+b_e epsilon_e a).

Every summand is a basis fraction: its denominator consists of a and one
independently shifted version of each q_e. Therefore every coordinate
multiple omega_i R belongs to the span S_Delta of inverse products of
bases from one common finite arrangement Delta. Take Delta to contain every
nonzero cut form, shifted cut form, and coordinate form arising from every
canonical rooted oriented tree on the N labels. This includes all apex
placements; no apex-dependent quotient is being silently identified.

The maximum has the same property directly:

    omega_j R_max = (-1)^(N-1) / product_(i!=j) omega_i.

Thus the map on the rational kernel space

    R |-> (omega_0 R,...,omega_(N-1) R) in (S_Delta)^N

is linear and injective. Its image satisfies

    sum_j F_j=0,             omega_i F_j=omega_j F_i.

Conversely these compatibility equations recover one rational R by dividing
any component by its nonzero coordinate form. The injectivity here concerns
rational kernels; no additional faithfulness theorem for arbitrary function
quotients is asserted or needed for the reduction.

## The complete descent condition

For a basis B=(beta_1,...,beta_r), write phi_B=1/product_i beta_i. If
alpha=sum_i c_i beta_i is another arrangement form, the exact identity is

    phi_B = sum_(i:c_i!=0) c_i phi_(B with beta_i replaced by alpha).

Multiplying by alpha product_i beta_i proves it immediately. Brion and
Vergne establish that these basis-exchange identities generate all linear
relations among basis fractions; this identifies S_Delta with the top
Orlik-Solomon space. Their iterated residues also give dual coordinates.
See [Arrangement of hyperplanes I, Section 4](https://arxiv.org/html/math/9903178#S4).

Consequently a proposed tensor assignment to basis fractions must satisfy
every such circuit relation, including relations mixing former apex roles.
Checking only the local six-term graft identity is insufficient. A map
satisfying this complete presentation would descend to actual rational
functions automatically, hence would respect every whole-function identity.

The Fourier map already kills the full lower-dimensional span generically.
Composing it with the marked embedding and an established linear map on
S_Delta would therefore be a genuine top-quotient functional. This fixes
the descent problem in principle; it does not construct the needed map.

## Why the mark cannot be discarded

A scalar functional on the marked space can have the form

    Lambda(R) = sum_j ell_j(omega_j R).

Using the same ell for every j gives zero because sum_j omega_j=0. A
permutation-invariant construction must use a covariant family of marked
functionals, not discard the mark before contraction.

The symmetric graph top class from overnight_uniform_symmetric_complex.md
is one possible target. Its Pfaffian sign needs an orientation factor before
scalar contraction. The remaining task is an explicit marked assignment to
basis fractions satisfying the full circuit relations, annihilating every
outward-twin canonical unit, and detecting the maximum at every sufficiently
large odd arity. No such assignment is supplied here. The finite N5 star
certificate and the exact twelve-term function relation remain mandatory
controls for any proposal.
