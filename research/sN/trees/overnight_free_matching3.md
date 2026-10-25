# Canonical matching-number-three trees can be adjoined for free

25 October 2026. Uniform consequence of the complete exact nine-label
separator, independently reviewed. Not Lean verified. This extends the
previous free-star and matching-number-two classes; it does not cover
unbounded sublinear matching number.

Let C_3 consist of every canonical tree face function whose ORIGINAL tree
has matching number at most three, with arbitrary shape, apex, head root,
edge orientation, and face state. At each arity m>=9 there is a linear
functional modulo L_(m-2) which kills C_3 and is nonzero on max_m.

Indeed use the coordinate-deletion operator

    T_j g = (partial_(-e_j)g - partial_(e_j)g) after inserting x_j=0.

It lowers L_d to L_(d-1): if coordinate j is constant on a polytope the two
exposed faces cancel, and otherwise both have smaller dimension. Restriction
cannot increase dimension. It sends max_m to max_(m-1).

For a full canonical tree unit, a top-dimensional surviving term can arise
only by deleting a leaf. Its remainder is a signed smaller canonical tree
unit, possibly with the head transferred to the adjacent vertex, modulo
the lower filtration. Deleting the apex leaves a zonotope; deleting a
nonleaf fixes at least two generators and drops an extra dimension.
A nonhinge state is already below the top filtration. These are the same
local face computations used for the previous free-star class and do not
use any restriction on the other branches of the tree.

Deleting a leaf cannot increase matching number. Compose m-9 deletions with
the certified nine-label separator from `overnight_lower_nine_bridge.md`.
The target becomes max9, each surviving C_3 term still has matching number
at most three, and every lower-dimensional remainder lies in L_7. This
proves the claimed separator at every m>=9.

At a generic tied locality of size m, a surviving canonical top germ is
an induced subtree with a transported head. Its matching number cannot
exceed the original matching number, so all C_3 terms vanish under the
local separator. Every other term which survives must pass the same
full-dimensional locality test as in the existing counting proofs.
Assign overlaps to C_3 first; count only terms outside this free class.

Consequently all fixed-size asymptotic bounds in
`overnight_free_class_asymptotics.md` hold with C_3 added. In particular,
adjoin C_3 to both the caterpillar and specified rooted-star face dictionaries
and to arbitrary weighted, arbitrary-head comparison graphs of fixed maximum
degree Delta. The number Z of terms outside C_3 satisfies

    Z = Omega((7/6)^N/sqrt(N))                  for Delta <= 3,
    Z = Omega_Delta((1+y_Delta)^N)              for Delta >= 4,
    y_Delta = (Delta-2)^(Delta-2)/(Delta-1)^(Delta-1).

Those proofs use tied sizes growing linearly with N, hence eventually at
least nine; no asymptotic factor is lost.

For the matching-mixture theorem, taking m=floor(N/4) gives, for N>=36
and 0<=2k<=N,

    Z >= (16/13)^k / [20(1+3k/13+9 binom(k,2)/169)].

Here the counted additional functions have arbitrary real heads and
comparison weights on pseudoforests with matching number at least k.
The two original dictionaries remain included. The corresponding bounded-
excess variant also holds, with denominator

    20 sum_(j=0)^(b+2) binom(k,j)(3/13)^j,

under its existing condition b+2<=N/4. Thus k=Omega(N), b=o(N) still gives
an exponential rate after adjoining C_3 for free.

Only the separately counted graph family allows arbitrary real heads and
weights. The free class C_3 is canonical, with unit comparison lengths and
a coordinate-difference head. This scope distinction is essential.

This is research-only; the paper's matched five-input section is unchanged.
