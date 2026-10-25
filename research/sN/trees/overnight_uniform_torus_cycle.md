# The coordinate torus-cycle control

25 October 2026. This is a failed exact contraction of the faithful
multiplicative kernel, retained to avoid repeating the same route.

At N5 put F_R=product_i(1-z_i)G_R, so F_max=1, and eliminate
z0=(z1 z2 z3 z4)^(-1). For each two-torsion character chi with
product_i chi_i=1, use the actual iterated rational residue

    Lambda_chi(F) = Res_(z4=chi4) ... Res_(z1=chi1)
                    F product_(i=1)^4 dz_i/(z_i-chi_i).

The order is z1,z2,z3,z4. Collisions with a unit's own poles are retained;
the operation is not mere substitution at chi. This defines a linear
functional on the actual rational-function space, with no tree-presentation
choices or later descent assumption.

For the unaveraged full S5 outward-star orbit, the values in lexicographic
order chi1,...,chi4 in {+1,-1} are

    36,36,36,36,36,36,36,36,36,36,36,36,60,60,36,84.

The maximum gives1 at each character. Summing all characters gives672 on
the star and16 on the maximum. Removing the identity character gives636
and15, respectively. Thus neither natural sum annihilates outward twins.

The producer uses exact Taylor quotient coefficients. The independent
checker starts with the unsimplified multiplicative kernel and performs
direct symbolic residues, without importing the producer. It verifies all
16 character values in15.24 seconds. Adjacent JSON receipts record source
hashes and exact outputs.

This closes this coordinate order and these unweighted sums, not every
possible torus cycle. No sweep over orders or fitted character weights is
claimed or undertaken.
