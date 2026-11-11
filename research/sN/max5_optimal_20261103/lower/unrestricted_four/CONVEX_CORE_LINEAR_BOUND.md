# A linear lower bound for convex or concave residual cores

Status: Lean verified, with an independent mathematical audit. The exact
convex-or-concave statement and raw biased-array statement are
`shape_bound` and `raw_shape_bound` in `convex_general/Shape.lean`;
`max5_two_core_impossible` is its MAX5 specialization. The fresh private
build in `convex_general/receipt.json` covers 95 local Lean sources,
290 hashes, and 37 standard-axiom audits. The physical-width corollary
remains a separate mathematical result in this checkpoint.

This replaces the longer convex-cover argument for two MAX5 cores with
an induction valid at every arity.

## Theorem

Let `N>=3`. Suppose, on every real input,

    MAX_N(x) = R(x) + sum_{j=1}^K d_j ReLU(g_j(x)),

where `R` and the `g_j` are arbitrary finite affine shallow ReLU functions,
the output coefficients `d_j` are arbitrary reals, and each `g_j` is either
globally convex or globally concave. Then

    K >= N-2.

There is no bound on first hidden width, no restriction to coordinate
differences, and no restriction on any bias. The cores and remainder may
use different dictionaries. The theorem counts folded residual cores in
the displayed identity; a conversion to physical second hidden width
needs its own architecture argument.

Consequently MAX5 cannot have two such residual cores. Every two-core
MAX5 identity must contain a preactivation that is neither convex nor
concave. For homogeneous shallow cores, this means that at least one core
has both positive and negative consolidated first-hyperplane curvature.
Oppositely oriented or repeated physical rows must be consolidated before
using that coefficient interpretation.

## Proof

Complement each concave core by the exact identity

    ReLU(g_j)=g_j+ReLU(-g_j),

absorbing `d_j*g_j` into the shallow remainder. We may therefore assume
all cores convex. We prove the bound by induction on `N`.

For `N=3`, a putative violation has no cores. But MAX3 is not shallow:
the directional germ at the origin of a finite affine shallow function
is homogeneous shallow and has a linear odd part, whereas MAX3 does not.

Suppose `N>=4` and the result holds for `N-1`. If there were fewer than
`N-2` cores, pad with zero convex cores to obtain exactly `K=N-3`.
Fix any input `q` with precisely `N-1` coordinates tied at the maximum.
Every core must vanish at `q`. Indeed, if one were nonzero, taking the
one-sided directional germ at `q` would turn its outer ReLU into a
shallow term or zero. Restrict directions to the tied coordinates. The
target germ is MAX_(N-1), while the remaining expression has at most
`N-4` folded convex shallow cores. The derivative of a convex shallow
function is again convex and shallow. This contradicts the inductive
lower bound `(N-1)-2=N-3`.

Now fix any input `x`. Choose `M>max_i x_i`, and define

    s=sum_i (M-x_i)>0,
    q_i=M*1-s*e_i,
    lambda_i=(M-x_i)/s.

Every `q_i` has exactly `N-1` maximizing coordinates. Moreover

    lambda_i>0,    sum_i lambda_i=1,    x=sum_i lambda_i*q_i.

Every core vanishes at every `q_i`. Convexity therefore gives

    g_j(x) <= sum_i lambda_i*g_j(q_i) = 0.

Since `x` was arbitrary, all outer ReLUs vanish identically. The supposed
identity says MAX_N equals its shallow remainder, contradicting the MAX3
restriction. This completes the induction.

## Why the local operation preserves the hypotheses

For a finite affine shallow function

    S(x)=a.x+b+sum_r c_r ReLU(A_r.x+beta_r),

its directional germ at `q` is

    D_q S(y)=a.y
      +sum_{A_r.q+beta_r>0} c_r A_r.y
      +sum_{A_r.q+beta_r=0} c_r ReLU(A_r.y).

This is an exact first-order expression for sufficiently small positive
steps in each fixed direction. It is a finite homogeneous shallow
function. If `S` is convex, its directional germ is convex: apply the
convexity inequality to `q+t*y` and `q+t*z`, subtract `S(q)`, divide by
`t>0`, and use the exact germs. Restriction to a linear coordinate
embedding also preserves convexity and shallowness.

The outer germ is zero when `g_j(q)<0`, is `D_q g_j` when `g_j(q)>0`,
and is `ReLU(D_q g_j)` when `g_j(q)=0`. Thus a nonzero core value really
does remove that folded core. No differentiability at a first-layer
wall, generic-position assumption, or exclusion of zero plateaus is
needed. Biases are handled by this formula directly; recession is not
required.

## Use for the MAX5 search

This transfers the localization mechanism from the general lower bounds
into a first-width-independent structural exclusion. It rules out a
natural class of candidate two-core identities, including mixtures of
convex and concave cores and arbitrary outer signs. It also explains why
making every core convex is not a harmless normalization of a possible
two-core solution.

It does not exclude arbitrary two-core identities, whose cores can have
curvature of both signs. Nor does it close the physical `(9,4)` problem
or change the unrestricted ordinary-network interval `4 <= h2 <= 6`.
The explicit invisible shallow function in
`topology/INVISIBLE_SHALLOW.md` shows why local contact data alone do not
control those unrestricted cores.

Independent audit: `topology/CONVEX_CORE_LINEAR_BOUND_AUDIT.md`.
The earlier convex-cover proof remains in `CONVEX_CORE_OBSTRUCTION.md`
as an independently checked alternative for the two-core case.
