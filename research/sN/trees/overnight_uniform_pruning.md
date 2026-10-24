# Matched-pair pruning and the all-apex infinity recursion

25 October 2026. The unrestricted all-tree exponential lower bound remains
open. This branch proves an exact full-symmetry pair-at-infinity identity,
including every apex placement. It also exactly refutes separation through
that leading projection alone. Retaining the next even inverse coefficient
restores the five-label separation in a small exact gate, but no uniform
matching recursion has been proved.

The prior paired-collision branch is preserved unchanged in
`overnight_uniform.md`. No paper or production Lean file is changed.

## Matching-closed deletion and the operator needed

If an even tree `T` has no perfect matching, then for **every** edge `uv`
the forest `T-{u,v}` has no perfect matching: a perfect matching of this
forest, together with `uv`, would be one of `T`. For a leaf `u`, every
perfect matching must contain its edge `uv`, so this is exactly the usual
forced-pair pruning recursion. The forest may have several components.

This closure does not hold for deleting two arbitrary vertices. Nor can
one fixed coordinate-deletion composition provide the desired separation:
adding two outward leaves at a common hub gives a bad even tree but deleting
those two labels recovers an arbitrary smaller unit. The existing
`reopen_lower_odd.md` gives the corresponding one-coordinate obstruction.

A useful linear reduction must therefore retain edge incidence, and must
control units whose apex is among the deleted labels. The operator below
makes both issues explicit, but initially produces a **marked contraction**
rather than deletion of both endpoints.

## Exact leading pair-at-infinity identity

Let `U` be a canonical rooted oriented tree unit on `N>=5` labels, with
apex `a`, root `r`, and tree `T` on the other `N-1` labels. Write

```
R_U(omega) = (-omega_a)^(N-4)
             / product_edges [Q_e(Q_e+epsilon_e omega_a)],
F_U = sum_(pi in S_N) R_U(omega_pi).
```

Here `Q_e` is the cut sum on the side away from `r`, and `epsilon_e=+1`
when the edge's positive endpoint is on that side. These are **full sums**,
not averages; automorphism multiplicities are retained.

Take `N-2` independent remaining frequencies `xi=(xi_1,...,xi_(N-2))`,
put `S=sum xi_i`, and define the linear operation

```
L F(xi) = lim_(z -> infinity) z^2 F(z,-z-S,xi).
J_N(xi) = (-1)^N / product_i xi_i.
```

The maximum kernel maps to `J_N`. Every canonical tree kernel has a finite
limit here. Statements are first made at generic frequencies away from all
relevant poles, and then as identities of rational functions.

For an edge `e`, contract it to a marked vertex `c`, inheriting the root and
all remaining orientations. Give `c` the fixed frequency `-S`. Let

```
B_(U/e,c)(xi) = sum_(bijections xi -> all other labels)
                  (-omega_a) R_(U/e)(omega).
```

The contracted unit has `N-1` labels. Its marked vertex is nonapex and can
be the root. Every one of the `(N-2)!` assignments to the other labels is
included.

Root `T` at `r` and let `Reach(r)` contain the vertices whose path from `r`
uses only edges with `epsilon_e=+1`. For any vertex `v`, let `e(T,v)` be the
number of linear extensions of the tree rooted at `v`, with each parent
before its descendants and with `v` omitted. Thus

```
e(T,v) = (N-2)! / product_(w != v) |subtree_v(w)|.
C_U = (product_e epsilon_e) sum_(v in Reach(r)) e(T,v).
```

The exact identity is

```
L F_U = 2 sum_edges B_(U/e,c) + 2 C_U J_N.                  (1)
```

The scalar `C_U` is always nonzero: its sign is the product of the rooted
edge signs and the sum contains at least the positive term `e(T,r)`.

### Proof, including all apex placements

If the apex receives a remaining finite frequency, each edge separating
the two large frequencies contributes two large denominator factors.
The decay is `z^(-2d)`, where `d` is the distance between their tree
vertices. Only adjacent vertices survive after multiplication by `z^2`.
Their edge factor has leading coefficient one. The other cut sums are
exactly those of the contracted tree with marked frequency `-S`; the
numerator changes from exponent `N-4` to `N-5`, leaving the factor
`-omega_a`. The two assignments of the large frequencies to the edge ends
give `2 B_(U/e,c)`.

If the apex receives a large frequency, call the nonapex vertex carrying
the other large frequency `v`. Every denominator off the path `r--v` has
one large factor. On this path, there is only one large factor precisely
when `epsilon_e=+1`; a negative edge contributes one extra large factor.
Hence only `v in Reach(r)` survives in the leading limit.

Rerooting at `v`, let `q'_e` be the finite-frequency sum in its away
component. The signs from the large path factors cancel those from the
reversed small cut sums. The leading summand is

```
(-1)^N (product_e epsilon_e) / product_e q'_e.
```

The rooted-tree shuffle identity gives

```
sum_(bijections xi -> T\{v}) 1/product_e q'_e
       = e(T,v)/product_i xi_i.                          (2)
```

For positive `xi`, one proof writes the left summand as the Laplace
integral on `0<=s_parent<=s_child`. Partition this cone into its `e(T,v)`
linear-extension cones. Symmetrizing the frequency assignments on each
cone fills the positive orthant once and gives `1/product xi_i`. The
rational identity then follows on the full generic domain. Both choices
of large-frequency apex have the same sign, yielding the second term of
(1).

### Independent controls and review

`overnight_uniform_pruning_infinity.py` compares two parameterizations:
normalized heads/positive-endpoint cuts directly compute Laurent degrees,
while rooted-away cuts compute the contraction side and the hook counts.
All arithmetic is rational. It checks:

- all 26 canonical rooted/oriented five-label tree orbits;
- three structured seven-label units;
- the nine-label subdivided claw with arm lengths `1,3,3`, which has no
  initial twin leaves and no perfect matching.

The small phase took 0.19 seconds; the claw phase checks all `9!` assignments
and took 7.97 seconds. Receipts are
`overnight_uniform_pruning_infinity_small.json` and
`overnight_uniform_pruning_infinity_claw9.json`.

The independent fixed-layer proof agent reviewed (1) and (2), confirming
the signs, the unaveraged multiplicities, and the generic-frequency scope.
This is a mathematical identity with finite exact controls, not a Lean
verification result.

## Exact rejection of the leading projection as a separator

The two canonical five-label stars below have apex0, root1, and centre2.
An ordered edge `(u,v)` means the inner function `sigma(x_u-x_v)`:

```
U_0: (2,1), (3,2), (4,2)
U_1: (2,1), (3,2), (2,4).
```

For `xi=(1,r,s)`, define

```
A = 3 r^2 s + 3 r^2 + 3 r s^2 + 3 r + 3 s^2 + 3 s,
D = r s (r+1)(r+s)(s+1).
```

Direct symbolic calculation gives

```
L F_(U_0) = -12 (A+4rs)/D,
L F_(U_1) =   8 (A+8rs)/D,
L F_(U_0)/72 - L F_(U_1)/48 = -1/(rs) = L R_max5.       (3)
```

Homogeneity extends this identity to all three remaining frequencies.
Thus no linear functional applied **after this leading projection alone**
can separate the maximum from the bad-tree family. This rejects an entire
rational-function reduction, not only finitely many frequency evaluations.
It does not refute the actual matching separator or the all-tree lower bound.

The finite producer is `overnight_uniform_pruning_gate.py/json/log`.
The standalone checker `overnight_uniform_pruning_identity_check.py/json/log`
reads only the two star descriptions and the proposed coefficients. It
independently rebuilds normalized heads, computes all 120 leading Laurent
terms symbolically, and verifies (3) over `Q(r,s)`. It does not use the
contraction formula, the hook counts, the producer's evaluator, or the
finite grid. Its exact check took 5.27 seconds.

## Retaining the first correction: current live branch

Use the symmetric frequencies

```
(z-S/2, -z-S/2, xi).
```

The full orbit function is even in `z`, so only even inverse powers occur.
The maximum has first coefficients

```
[z^-2] R_max = J_N,
[z^-4] R_max = (S^2/4) J_N.
```

At five labels, retaining both coefficients yields exact ranks `5/6` on
all ten star orbit columns. `overnight_uniform_pruning_jets.py/json/log`
records 20 exact rows, a rational annihilator, and two controls: the
`z^-3` coefficient vanishes, and every leading coefficient agrees with the
independently derived contraction identity. The run took 1.48 seconds.
This is a finite five-label result only; it does not establish a uniform
operator or a matching recursion.

The next task is to express the correction through marked forests while
retaining all apex placements. In the finite-apex part, adjacent outliers
produce a quadratic cut-moment correction to the marked-edge contraction;
outliers at distance two produce a marked three-vertex-path contraction.
The latter term omits the original middle vertex's independent frequency.
The adjacent correction remembers how neighbours were split between the
two contracted endpoints, data absent from an ordinary marked contraction.
A valid induction therefore needs more boundary data than (1).

## Full second-coefficient formula and independent controls

Write `L_2 F=[z^-4]F(z-S/2,-z-S/2,xi)` and `k=N-4`.
The following descriptions apply to every fixed assignment of the finite
frequencies, before its full sum.

For a finite apex, only outlier distances one and two contribute.
For adjacent outliers, let `c` be the constant part of the away-root cut
sum on their edge, so that its two factors are
`(epsilon_z z+c)(epsilon_z z+c+epsilon_e a)`.
The correction to the leading marked-contraction summand is

```
3 c^2 + 3 c epsilon_e a + a^2.                            (4)
```

Both outlier assignments give the same value. If the outliers have distance
two, the leading coefficient after multiplying by `z^4` is obtained by
contracting their whole three-vertex path and multiplying its kernel by
`a^2`. The frequency of the marked vertex becomes
`xi_middle-S=-sum(other xi)`. Therefore this term is independent of the
original middle vertex's independent frequency. Distances at least three
contribute zero to `L_2`.

For an outlier apex, reroot the nonapex tree at the vertex `v` carrying the
other outlier, and write `q'_e` for the finite subtree sums. Retain the
original edge signs `epsilon_e` rooted at `r`. Let `P_v` be the path
`r--v`, let `B_v` be its negative-sign edges, and put `b=|B_v|`.
Only `b<=2` can contribute. Form the multiset `rho` consisting of

```
q'_e-S/2          for e on P_v,
epsilon_e q'_e-S/2 for e off P_v,
(q'_e-S)/2        additionally for e in B_v.
```

Define

```
H_0 = 1,
H_1 = -k S/2 - sum rho,
H_2 = binom(k,2) S^2/4 + (k S/2) sum rho + h_2(rho).
```

After summing both outlier-apex choices, this vertex's contribution is

```
2 (-1)^N (product_e epsilon_e) (-1/2)^b
    * Sym_xi [ (product_(e in B_v) q'_e)
               H_(2-b) / product_e q'_e ].              (5)
```

Here the sum assigns every finite frequency to a vertex other than `v`.
Formula (5) is the coefficient of degree `2-b` in

```
(1-S t/2)^k product_(rho_j in rho) (1+rho_j t)^(-1),
```

with the leading factor displayed in (5). It explicitly includes the
wrong-oriented root-path cases with `b=1,2`; dropping those cases is invalid.

`overnight_uniform_pruning_second_check.py/json/log` independently compares
(4),(5) and the distance-two terms with the normalized-head Laurent producer
on all 26 five-label orbits and the same three seven-label units. All 29
checks pass in 1.56 seconds. It also directly varies the distance-two middle
frequency and verifies that the corresponding term stays unchanged.

This formula exposes additional boundary data rather than closing a
recursion: (4) remembers the partition of branches between the contracted
edge endpoints; (5) contains quadratic weighted shuffle moments, not merely
the ordinary hook counts of (1).

## Extracting the complete all-remaining-label cut residue

Let `eta_1+...+eta_(N-2)=0`, and take the residue at `S=0` before discarding
any powers of `z`. The maximum kernel is regular at this cut, so its residue
is zero. At generic `eta,z`, the only individual tree terms which can have
a pole are:

1. A finite apex, with the two outlier vertices forming an entire pendant
   two-vertex component of the nonapex tree.
2. An outlier apex, whose other outlier vertex is a nonapex leaf.

For case1, the root-side cut can require a positive orientation sign. For
case2, a nonroot partner leaf must have its positive endpoint at that leaf;
a root partner leaf has a different cut factor. These orientation conditions
must be retained. The pole classification is necessary, not a claim that
all poles survive the complete permutation sum. It follows because the
only zero generic cut sums are the sum of all finite labels, or its
complementary outlier pair; the shifted cut factor additionally determines
the orientation. Exclude other partial-sum poles and `z=±eta_i` while taking
this first residue.

The fixed-layer proof agent independently checked this classification and
the need to retain both outlier-apex leaf placements. It also checked the
homogeneity and the cancellation in the identity below; it did not recompute
the three individual numerical constants.

For the two stars in (3), put

```
p_2 = eta_1^2+eta_2^2+eta_3^2,
D(z) = product_(i=1)^3 (z^2-eta_i^2).
```

The exact full cut residues are

```
Res_(S=0) F_(U_0) = 12 p_2 / D(z),
Res_(S=0) F_(U_1) = (-48 z^2+8 p_2) / D(z),
Res_(S=0) (F_(U_0)/72-F_(U_1)/48) = z^2 / D(z).          (6)
```

Thus the leading-projection identity has a nonzero boundary residue. Its
first term is `z^-4` with coefficient one. Equivalently, the error of that
same two-star combination in the next inverse coefficient is

```
-x y z / [(x+y)(y+z)(x+z)(x+y+z)],                      (7)
```

for the three remaining frequencies `x,y,z`; its residue at their total
sum zero is one. `overnight_uniform_pruning_correction.py/json/log` verifies
(7) symbolically. `overnight_uniform_pruning_cut_residue.py/json/log`
independently computes (6) directly from the full normalized-head kernels,
not by taking residues of the correction formula.

The exact small gate retaining the full leading function **and** the full
cut-residue function gives ranks `5/6` for all ten star orbits. Its data and
rational annihilator are in `overnight_uniform_pruning_residue_gate.*`.
This is a discriminating test of the proposed boundary data at the smallest
arity, not an all-arity extrapolation.

### A cancellation that any recursion must respect

The first star has zero `z^-4` cut-residue coefficient despite its nonzero
full cut residue. There is a uniform version. Take a star with root at one
leaf, its root edge oriented toward the centre, and every other leaf edge
oriented toward its leaf. Let `d=N-2` be its odd number of leaves, and let
`e_j` be the elementary symmetric polynomial in the `d` finite frequencies
of total sum zero. Then

```
Res_(S=0) F_U =
  2 d! p_2 z^(d-3) sum_(j>=3 odd) e_j z^(d-j)
  / [e_d product_i(z^2-eta_i^2)].                        (8)
```

To prove (8), every eligible partner is one of the `d` leaves. Removing it
leaves a star, and its finite-frequency sum is
`(d-1)! p_2/[product eta_i product(eta_i+z)]`.
Adding the two apex choices retains the even part; `e_1=0` removes the
apparent earlier term. Formula (8) starts generically at `z^-6`, not `z^-4`.
A direct exact seven-label control is included in the cut-residue receipt.
This demonstrates why retaining only a presumed first surviving boundary
coefficient can lose information.

## A precise combinatorial matching invariant; analytic bridge still open

For any orientation of an even tree, let its edges generate a poset. Its
signed number of linear extensions is zero exactly when the tree has no
perfect matching. Swap the first incomparable consecutive pair in positions
`(1,2),(3,4),...`; this reverses sign. Survivors form domino extensions.
A tree has at most one perfect matching. If it has one, contract its edges:
the quotient is an oriented tree, hence admits a linear extension. Ordering
these two-element blocks gives all survivors. Block swaps have even parity,
so every survivor has the same sign. The absolute imbalance is the number
of extensions of that contracted oriented tree.

This uses the domino/sign-balance framework in
[Stanley's primary survey, Section4](https://arxiv.org/html/math/0211113).
`overnight_uniform_pruning_signbalance.*` checks all even tree shapes through
eight vertices and every orientation, comparing signed subset DP against
forced-pair pruning and unsigned DP on the contracted matching tree.

The rational shuffle formula currently gives **unsigned** extension counts.
A single alternating functional also kills the symmetric maximum. No
linear polarization or two-factor construction has yet turned the signed
invariant into a functional on the actual full rational kernels. That bridge,
including the outlier-apex terms, remains open.

## Signed-root score descent gates

The sign-balance lemma supplies a necessary zero on every non-perfect-matchable
shape, but that alone does not define a linear functional on Fourier kernels.
There are nontrivial relations between different shapes. Write `a>b` for the
positive endpoint `a` in an oriented edge. Direct normalized-head polynomial
arithmetic proves the all-frequency identity at five labels

```
F_(root1; 2>1,3>2,4>2) = 3 F_(root1; 2>1,1>3,2>4).      (9)
```

The left tree is a star; the right tree is a path and has a perfect matching.
Thus a valid matching separator must also vanish on some perfectly matchable
units. `overnight_uniform_pruning_signed_relation.*` verifies (9) independently
of the finite evaluation producer: all240 permutation summands, a common
polynomial denominator, and identically zero numerator in three free ratios.
The check took47 seconds. This refutes the first candidate
`sum_(v<w in A) (-1)^dist(v,w) I_v I_w`, whose two scores are0 and−1.

Here `I_v` is the signed number of extensions of the tree oriented away from
`v`, `A` is the component of the head root using edges with `epsilon=+`, and
`epsilon=product_e epsilon_e`. These data are invariant under changing the
canonical head-root representation without changing the function: moving
across a positive edge and reversing its actual orientation preserves the
root-relative edge signs and the component `A`.

A corrected, simple five-label score is

```
Q(U) = (sum_(v in A) I_v)^2 + (sum_(v in A) chi_v I_v)^2
       - (1+epsilon)/2 sum_v I_v^2,                    (10)
```

where `chi_v=±1` is either bipartite coloring. There is an exact evaluation
functional with `L(F_U)=-15 Q(U)` on every five-label rooted oriented tree,
and `L(R_max)=1`. The standard-library checker
`overnight_uniform_pruning_signed5_check.*` independently covers all26
root/orientation orbits via all labelled Pruefer trees, sums normalized-head
kernels directly over `S_5`, and counts signed extensions by all24 vertex
orders. It checks twelve rational evaluation weights in0.3 seconds. This is
an exact five-label statement only.

For clarity, (10) also follows from a quadratic distance expression. When a
perfect matching exists, the two roots in each matched pair have opposite
signed extension counts; every other matching pair lies entirely on one side
of any nonmatching-edge cut. Hence `sum I_v=0`, and the tree-distance identity

```
sum_(v,w) dist(v,w) I_v I_w
  = -2 sum_edges (sum_(v in one cut side) I_v)^2
  = -sum_v I_v^2
```

holds. Without a perfect matching all counts vanish, so it holds there too.

The full seven-label modular gate covers458 root/orientation orbits. Its
320 rows have rank175, stable from row200 onward. Score (10) does not belong
to this sampled row space. The entire small family using only distance
powers0–2, bipartite parity, positive-root-component membership, and the
orientation product has no target-detecting score in this gate. Adding
`kappa_v+kappa_w`, `kappa_v kappa_w`, and `(kappa_v-kappa_w)^2` admits scores;
this is a modular diagnostic, not an exact seven-label identity certificate.

One sparse candidate passes both five- and seven-label modular gates. Set

```
D_j   = sum_(v,w) dist(v,w)^j I_v I_w,
D_j^c = sum_(v,w) dist(v,w)^j chi_v chi_w I_v I_w,
K_j   = sum_(v,w) dist(v,w)^j (kappa_v+kappa_w) I_v I_w,
K_j^c = sum_(v,w) dist(v,w)^j chi_v chi_w
                       (kappa_v+kappa_w) I_v I_w.
```

The candidate is

```
(15/8) [36 D_1 - 2 K_1 + 2 epsilon D_1
        - 6 K_1^c - 2 epsilon D_1^c - 3 epsilon D_2].   (11)
```

Its sampled maximum responses are1 at five labels and1/28 at seven labels,
modulo1000003. These coefficients are only a small rational reconstruction
of the one-prime solution. No all-arity formula, descent proof, or exact
seven-label response is claimed. The larger feature space has many surviving
scores, so this fit should not be interpreted as a uniqueness result.
Files `overnight_uniform_pruning_signed_family.*`, `_signed7.*`, and
`_signed_joint.*` retain the gates. The latter stores only the three sparsest
selected candidates; the producer records the count of all passing basis
candidates. There was no new nine-label generic rank run.

## A rational pruning operation with no hidden apex assumption

The separate note [Complete paired-cut residue](overnight_uniform_pruning_residue.md)
now gives the full all-apex recurrence, including its smaller marked kernels.
It proves that `Res_(z=2 eta_i) Res_(S=0)` cleanly deletes a pendant pair when
the head root begins a path with signs `(-,+)`, and otherwise gives zero.
The resulting lower kernel has its apex fixed at `eta_i`. It preserves
failure of perfect matching, handles every apex placement, and has an
independent semantic audit. The maximum maps to zero, so it is a relation
constraint rather than a separator by itself. This is the current structural
advance beyond the finite signed-score gates.

A possible discrete-generating-function shortcut requires separate proof.
[Kim and Stanton](https://arxiv.org/abs/1608.03342) connect order-polytope
q-integrals to linear-extension generating functions, but their integral
depends on integration order. [Lenz](https://arxiv.org/abs/1408.4041) describes
Todd-operator links between spline densities and lattice-point enumerators;
the operator depends on the generating vector configuration. Neither result
automatically supplies one linear map on our rational-function quotient.
Replacing each rooted shuffle by its signed or q-specialized count still
has to respect relations such as (9). No such lift has been asserted.

## Current residual

The next candidate is a boundary-compatible linear separator using the
leading pair-at-infinity function together with its complete proper-cut
residues. Pendant two-vertex components reduce by matched-pair deletion;
the other-apex terms reduce to a leaf-removed tree with an external apex
parameter and a marked attachment vertex. Neither that external parameter
nor the quadratic shuffle data can currently be discarded. A uniform
projection compatible with these boundary terms, or a proof that the
matching invariant descends through their rational relations, is still
needed. The exact leading-projection counterexample (3) prevents reverting
to an induction that forgets this boundary information.
