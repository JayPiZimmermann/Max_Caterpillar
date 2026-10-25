# The factorial dimension bound from the common local test

Status: complete mathematical proof for every N≥3. This is a shorter human
proof of the existing theorem q_N≥(N−2)!, not a new Lean declaration. It uses
the same local simplex class as the counting proofs and replaces the third
mixed difference, eight corners, and cube-margin calculation. No independence
modulo L_(N−2) is asserted.

## The proof

Put r=N−2 and b=N−1. For each ordering pi of the r middle labels, let
pi(r+1)=b and take the existing dictionary path function

    U_pi(x) = sigma(x_b−x_0 + sum_(j=1)^r sigma(x_pi(j)−x_pi(j+1))).

There are r! such functions. Fix another ordering rho and set c=rho(r).
Choose the point

    p_0=p_b=1,       p_rho(j)=1+j−r  (1≤j≤r).

Exactly T={0,b,c} ties at the top; all other coordinates are distinct and
smaller. Let E_T insert zero perturbations outside T, and let J_0 insert
zero in the tied coordinate 0. Consider the linear, quotient-valued test

    G_rho f = [ (partial_p f) composed with E_T composed with J_0 ]
                modulo L_1 on R^{ {b,c} }.

Here partial_p denotes the directional germ, as in the common locality
lemma. Every auxiliary function is shallow; germs and linear restrictions
preserve L_1. Consequently G_rho annihilates A_N.

For pi=rho, all middle path comparisons are strictly negative at p, and only
the last comparison, x_c−x_b, is tied. The outer preactivation is zero.
Therefore the tied-coordinate germ is exactly

    sigma(y_b−y_0 + sigma(y_c−y_b))
      = max(y_0,y_b,y_c)−y_0.

Anchoring y_0=0 gives max(0,y_b,y_c), whose class v in the quotient by L_1
is nonzero: it is the support function of a triangle. This is the same
simplex-nonvanishing fact already used in the common local test.

For pi≠rho, the middle labels in pi order are not increasing in rho height.
An adjacent strict descent therefore exists. At p its inner ReLU is strictly
positive, while x_b−x_0=0 and every other inner term is nonnegative. The
outer preactivation is thus strictly positive. Its germ is consequently
shallow, and G_rho U_pi=0.

Identifying the two remaining coordinates in the order (b,c), we obtain

    G_rho U_pi = v if pi=rho, and 0 otherwise,        v≠0.

If sum_pi a_pi U_pi belongs to A_N, applying G_rho gives a_rho v=0, hence
a_rho=0. Thus the r! path functions are independent modulo A_N and
q_N≥r!=(N−2)!.

For r=1 there are no lower coordinates and no distinct ordering pi. The
point is (1,1,1), the selected germ is the same triangle, and the argument
proves q_3≥1 without a separate case or an empty-descent assumption.

## Compatibility with either common-test formulation

The first anchored germ above is enough. If the paper retains the earlier
second derivative in the all-ones tied direction, the proof is unchanged:
the selected germ max(y_0,y_b,y_c)−y_0 is translation invariant and is fixed
by that derivative, whereas the off-diagonal germs remain shallow.

The first-germ-only common lemma also suffices throughout the counting
proofs, using generic points instead of digits. Fix an outside order and
consider the open stratum p_t=1 for t in T, with outside coordinates
distinct, in the prescribed order, and below1. Each preactivation restricts
there to an affine function lambda+sum_o b_o p_o. After fixing the finite
expansion, choose p away from the zero sets of all restrictions that are
not identically zero. A(p)=0 then forces every b_o=0 and lambda=0. The
isolated tied-coordinate argument has both kernel directions 1_T and e_t,
including when t is the anchor. For T containing all labels the stratum
is a point and the same assertion is immediate. Biases are first removed
by recession.

This generic argument works for real heads. With unit inner coefficients,
the combinatorial passing proof also has exactly the same scope: outside
counts are integers in [0,degree_i], while tied isolated activity only
tests kappa_i≠0. Replacing any kappa_i outside this finite integer range
by degree_i+1 preserves every passing condition and every zero-kappa
pendant. It gives an integer-head description of the same passing set,
so the existing integral combinatorial count applies. This broadening is
a mathematical consequence, not a claim that the new analytic bridge has
been formalized in Lean. Arbitrary-weight units use the graph-rank
condition c(G[T])≤2; their reduced-forest bound is not asserted here.

The dimension points need no powers: their only required properties are the
strict order below the top and the unique adjacent tie. A zero lower
coordinate causes no difficulty because auxiliary germs are still shallow.

## Why the triple germ is preferable to one generic kink

At this isolating configuration the selected function is locally
max(y_0,y_b,y_c)−y_0. On either side of the inner comparison wall its outer
wall is a coordinate-comparison wall already present in the auxiliary
span. A jump on only one generic wall therefore does not by itself remove
that auxiliary ambiguity. The triangle class retains their junction and
annihilates every shallow summand at once. A separate search for a unique
outer hyperplane is unnecessary.

If scalar rather than quotient-valued tests are desired, an explicit
functional on a two-variable germ F is the difference of normal slope
jumps across s=0 at (s,t)=(0,−1) and (0,1):

    J(F) = partial_(0,−1)F(1,0)+partial_(0,−1)F(−1,0)
         − partial_(0,1) F(1,0)−partial_(0,1) F(−1,0).

It vanishes on every linear function and every ReLU of a linear form.
Indeed, a linear form with nonzero t coefficient is nonzero at both base
points and gives zero slope jump; if that coefficient is zero, the two
jumps coincide. For F=max(0,s,t), J(F)=1. Thus J composed with the first
anchored germ gives an identity evaluation matrix as well. The
quotient-valued formulation is shorter when the common lemma is already
available.

## Exact scope and unification

The test annihilates A_N because A_N is shallow. It does not annihilate
L_(N−2) in the original N-variable space when N≥4: for example the function
max(x_0,x_b,x_c) belongs to L_2⊆L_(N−2) and has a nonzero tested triangle
class. Hence this proof must not be advertised as independence in the
ambient top-dimensional quotient.

The lower-bound section can therefore use one operation for both purposes:

* counting: every target locality has nonzero simplex class, so at least
  one dictionary term must serve it; bound each term's locality capacity;
* vocabulary dimension: the selected path family serves a diagonal set of
  local tests, so every coefficient is individually detected.

The remaining graph, orientation, matching, and star-block arguments only
bound capacities; they need not reprove the local analytic step. No paper
or Lean source has been edited by this audit.

The existing block count can also be summed across all tied sizes before
discarding weights. If a_U(T) denotes the fraction of outside orders passed
by a unit and A=T intersect Phi is its free-vertex set, then T is determined
by A across all sizes: isolated memberships are fixed, pendants follow
their hubs, and a component of two pendants is forced tied. Thus

    sum_(|T|≥3) y^|T| a_U(T)
       ≤ sum_A y^|A| 2^(−mu(A)) ≤ 1,

for y=1/(2 Delta+2). The block matching may depend on A; no common matching
across different tie sets is required. For source-oriented covering
subforests, the same product uses weight y for a forced singleton. Summing
the common locality coverage gives the exact tail bound

    |K| ≥ (1+y)^N−1−Ny−binom(N,2)y² = Omega((1+y)^N).

Here a_U is the combinatorial passing fraction, not a claim that the
actual germ is nonzero at every passed locality. This removes the former
N+1 loss without a separate asymptotic or concentration calculation.
