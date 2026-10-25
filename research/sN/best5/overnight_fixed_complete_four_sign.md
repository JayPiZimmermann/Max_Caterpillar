# A single negative outer unit cannot supply a max4 germ

Let V4 be the span of linear functions and sigma(x_i-x_j) on four labels.
There is no identity

    max4 = R - sigma(g)

with R,g in V4 and g invariant under common translation.

At every top-three tie, generic locality forces g to vanish; otherwise
the only outer ReLU linearizes there and the max3 germ would be shallow.
Consequently g(1_T)=0 for every three-element subset T. Also g(0)=g(1)=0.
Let p_i=sigma(g(1_{i})), q_ij=sigma(g(1_{i,j})), P=sum p_i, Q=sum q_ij.
The third Boolean mixed difference of R vanishes, whereas that of max4
on each triple is1. Thus

    sum_(pairs in T) q_ij - sum_(i in T) p_i = 1.

Summing over the four triples gives 2Q-3P=4. The fourth mixed difference
of R vanishes and that of max4 is-1, giving Q-P=1. These equations imply
P=-2, contradicting p_i>=0. No assumption of braid conformity is needed.
With a positive outer output instead, the same argument gives P=2, which
is consistent with the standard max4 construction.

For the max5 K3 model with output signs(+,+,-), this implies that every
quadruple ray has a zero preactivation among the two positive-output
units. Indeed locality requires some zero core there. If both positive
cores are nonzero, the only remaining unit is negative; taking the germ
at the top-four tie gives exactly the impossible identity above. The
preactivation germ is translation invariant within the tied coordinates:
its value at the tie ray is zero, and homogeneity implies its directional
derivative is unchanged by adding that ray. All untied first-layer
comparison functions become linear in this germ.

Thus the p2 quad cover can use only its two positive cores. Up to label
and positive-neuron permutations, its fiber sizes are(0,5),(1,4),(2,3).
These are already present in the bounded twelve-case campaign and did
not resolve within that run's15second caps. This lemma is a new necessary
condition, not K3 infeasibility. The elementary arithmetic contradiction
is separately Lean verified; the geometric bridge remains a written proof.
