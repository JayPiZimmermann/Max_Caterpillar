# Physical width at least N when every second preactivation has one curvature sign

Status: mathematical proof with an independent cold audit.
No Lean verification of this physical-network corollary is claimed here.
Its main input is the independently audited residual-core bound in
`CONVEX_CORE_LINEAR_BOUND.md`.

## Statement

Let `N>=3`. An ordinary two-hidden-layer ReLU network computing MAX_N on
all real inputs has second hidden width at least `N` if every second-layer
preactivation, considered as a function of the original input, is globally
convex or globally concave. Each neuron may make its own choice between
convex and concave. First width, all real weights, and all biases are
unrestricted. No skips are present in the physical network.

In particular, a physical MAX5 network with four second neurons must
contain a preactivation that is neither convex nor concave. This excludes
that curvature class at every first hidden width. It does not prove that
all width-four MAX5 networks are impossible.

## Translation tails

Homogeneous recession removes all biases without changing widths or
convexity/concavity. Write the second preactivations as finite homogeneous
shallow functions `G_k`, with signed output coefficients `d_k`.

For a shallow function G and the all-ones vector, its two exact eventual
translation expansions are

    G(x+t*1) = t*a + A(x)       for sufficiently large positive t,
    G(x-t*1) = t*b + B(x)       for sufficiently large positive t.

Here `a=G(1)`, `b=G(-1)`, and A,B are homogeneous shallow functions.
For each fixed x the equalities are exact beyond a finite threshold.
The first rows with positive coordinate sum contribute linearly to A
and zero to B; negative-sum rows do the reverse; zero-sum rows retain
the same ReLU at both ends. Consequently `A-B` is linear.

The intercept A is the one-sided directional derivative of G at `1`;
B is the derivative at `-1`. If G is convex or concave, the corresponding
intercepts retain that same property.

Applying the network identity at either end, nonzero second-layer slopes
become shallow terms or disappear. The zero-slope preactivations remain
folded cores. The residual theorem therefore requires at least `N-2`
zero slopes at each end. Since the output slopes are `+1` and `-1`,
each end also has at least one nonzero passing neuron. Thus `h2>=N-1`.

## Exclude equality

Suppose `h2=N-1`. Then each end has exactly one nonzero second slope.
Let p be the positive-end passer and q the negative-end passer. Their
output coefficients are respectively positive and negative, so `p!=q`.
All other `N-3` cores have `G_k(1)=G_k(-1)=0`.

A convex homogeneous function vanishing at both diagonal directions is
invariant under diagonal translation: subadditivity gives
`G(x+t*1)<=G(x)`, and applying it in the reverse direction gives equality.
For a concave function, apply the same argument to its negative. Thus
the common `N-3` cores are the very same functions at both tails; there
are no linear shifts between their two intercepts. Let H denote their
signed folded sum.

Absorb the positive magnitudes of the two passing outputs into their
preactivations, calling the resulting shallow functions P and Q. Their
outputs are `+ReLU(P)` and `-ReLU(Q)`. The two tail slopes normalize to
one. Write `P_+,P_-` and `Q_+,Q_-` for their intercepts. The output's two
intercept identities are

    MAX_N = P_+ - ReLU(Q_+) + H,
    MAX_N = ReLU(P_-) - Q_- + H.

Subtracting them gives

    (P_+-P_-) + (Q_--Q_+) = ReLU(-P_-) + ReLU(-Q_+).

The left side is linear, by the shallow translation-tail observation;
the right side is nonnegative everywhere. A linear function globally
nonnegative must be zero. Both terms on the right are therefore zero,
so `P_- >= 0` and `Q_+ >= 0` everywhere. The first identity reduces to

    MAX_N = (P_+-Q_+) + H.

This is a shallow remainder plus `N-3` folded convex-or-concave shallow
cores, contradicting the residual lower bound `K>=N-2`. Equality is
impossible, proving `h2>=N`.

## Scope of the improvement

The translation argument uses the actual original second preactivations.
Their two zero slopes and their convexity or concavity force the common
cores to be translation invariant. This is the extra reason why the
general shifted-tail obstruction disappears in this declared class.
For arbitrary shallow cores, equal zero slopes at both ends do not
imply translation invariance, and the argument cannot be applied.

The hypothesis is intrinsic convexity or concavity of each preactivation.
It is not simply a sign test on a redundant physical weight matrix.
Repeated or oppositely oriented first normals can cancel their curvature.

Independent audit: `topology/CONVEX_PHYSICAL_WIDTH_AUDIT.md`.
