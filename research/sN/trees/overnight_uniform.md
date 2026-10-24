# Uniform matching separator: paired-frequency branch

25 October 2026. The unrestricted all-tree exponential lower bound remains
open. This branch proves a useful matching-dependent vanishing-order lemma
for one apex placement, and exactly rejects the simplest fixed-normal
paired-residue separator. Allowing the normal to vary recovers separation
at five labels; at seven labels the first regular Laurent coefficient is
needed by the tested instrument. The nine-label jet test is underdetermined.
No new all-tree lower-bound theorem, exact nine-label separator, or Lean
certificate is asserted here.

## Target and the unresolved apex contamination

At odd arity `N=2q+1`, the proposed uniform theorem is that `max_N` is not in
the span, modulo `L_(N-2)`, of all canonical units whose tree on `N-1`
nonapex labels has no perfect matching. Roots and edge orientations are
unrestricted. This is only the canonical unit model used by the existing
head-flow/face bridge; arbitrary weighted edges or arbitrary heads are not
included. The conditional exponential counting consequence is recorded in
`reopen_lower_odd.md`.

For a rooted oriented tree, its generic Fourier kernel is

```
R_T(omega) = (-a)^(N-4) product_edges 1/[Q_e(Q_e + epsilon_e a)],
```

where `a` is the apex frequency, `Q_e` is the sum on the component away
from the root, and `epsilon_e` records the edge orientation. The maximum
kernel is `(-1)^(N-1)/product_i omega_i`. We use full permutation sums,
including automorphism multiplicities.

Set the base frequencies to `(0,+z_1,-z_1,...,+z_q,-z_q)`, with the `z_i`
linearly independent over the integers for the following structural proof.
Equivalently, they may be formal independent variables. Choose a generic
normal with equal values `p_i` on each opposite pair and value
`-2 sum_i p_i` on the zero label. Positive `p_i` avoid paths contained in
a pole. Write `omega(t)=base+t normal`.

### Uniform zero-apex lemma

If the unit's apex occupies the zero-frequency slot and its tree has
matching number `nu`, its individual kernel has Laurent order at least

```
N - 2 - 2 nu.
```

In particular, a tree without a perfect matching contributes no principal
part at this apex placement. Its order is at least one. More generally,
matching deficiency `q-nu=s` gives order at least `2s-1`.

Proof. Let `k` be the number of tree edges whose cut is a union of complete
opposite pairs. Exactly these edges have zero base cut sum. Each gives two
linear denominator factors vanishing at `t=0`; every other edge gives no
vanishing factor. The numerator has exact order `N-4`. Removing these `k`
edges leaves `k+1` connected components, each a union of complete pairs.
Every component has at least two vertices and hence contains an edge.
Choosing one edge from each component gives a matching, so `k+1<=nu`.
The Laurent order is exactly `N-4-2k`, which proves the bound.

Furthermore, order `-1` is possible exactly when the prescribed opposite
pairs themselves form the tree's perfect matching: then `k=q-1`, and all
`q` components after the cuts must be the prescribed two-vertex pairs.
Conversely, deleting the edges outside this matching gives these components.
This is a statement about one apex placement, not a universal prescribed
matching necessity for expansions.

### Uniform nonzero-apex bound

Suppose instead that the apex occupies `+z_i` or `-z_i`. The nonapex tree
then contains the zero-frequency vertex, the unmatched partner of that
apex, and `q-1` full opposite pairs. A vanishing denominator factor can
occur only on an edge cut separating none of those `q-1` pairs. There is
at most one vanishing factor per edge, because the base apex is nonzero.
If `k` such cuts occur, then

```
k <= nu + 1,   k <= q.
```

Indeed, removing the cuts gives components that are unions of intact pairs,
with at most two exceptional singleton components: the zero vertex and the
unmatched partner. At least `k-1` components therefore contain edges, giving
a matching of that size. Counting the `q-1` pairs and the two singletons
also gives at most `q+1` components. Orientations can remove an eligible pole,
but cannot create another kind of zero cut. Consequently the Laurent order
at a nonzero apex is at least `-min(nu+1,q)`.

The full orbit sum has odd Laurent parity: swapping the members of every
opposite pair sends the base to its negative and fixes the normal; kernel
homogeneity is degree `-N`. Hence every even Laurent coefficient vanishes.
These nonzero-apex terms are precisely the contamination not eliminated by
the zero-apex lemma. At seven and nine labels the possible principal powers
are therefore only `t^-3` and `t^-1`.

`overnight_uniform_pole_check.py` independently checks the underlying cut
counts for every unlabelled tree on 2,4,6,8 vertices, every opposite pairing,
and every assignment of the two exceptional vertices in the nonzero-apex
case. It does not use the Fourier producer or its subtree DAG. This is a
finite control for the proofs above, not their justification.

## Exact failure of the fixed-normal first residue

At five labels, fix base `(0,1,-1,z,-z)` and normal `(4,-1,-1,-1,-1)`.
Let `R_0,R_1` be the coefficients of `t^-1` in full permutation sums of the
following two canonical stars (apex0, root1, centre2):

```
T_0: (2,1), (3,2), (4,2)
T_1: (2,1), (3,2), (2,4)
```

The ordered edge `(u,v)` means the inner term `sigma(x_u-x_v)`. Exactly,

```
R_0 = (21 z^4 - 18 z^2 + 21) / [z^2 (z^2-1)^2],
R_1 = ( 2 z^4 - 36 z^2 +  2) / [z^2 (z^2-1)^2],
R_0/90 + R_1/120 = 1/(4 z^2).
```

The right side is the maximum's residue. Thus no linear functional of this
entire one-variable residue curve can separate the maximum from these two
stars. This rules out not only a single numerical evaluation but arbitrary
linear combinations of evaluations, secondary Laurent coefficients, and
contour integrals of this curve. It does not refute the full matching
separator or the actual lower bound.

Producer: `overnight_uniform_pair_residue.py/json/log`.
Independent checker: `overnight_uniform_pair_residue_check.py/json/log`.
The checker uses normalized heads and positive-endpoint cuts, not the
producer's rooted-away cut parameterization; it also uses explicit
pole-order formulas rather than the producer's convolution routine.

## Normal variation and regular jets: bounded evidence

Now use normal `(-2(1+r),1,1,r,r)` at five labels. The 49 exact rational
rows with `z=3,...,9`, `r=1,...,7` give ordinary/augmented ranks `5/6`
for all ten star orbit columns. The producer saves an exact rational
annihilator. A symbolic calculation over `Q(z,r)` gives the same ranks.
The special value `z=2` is excluded because it lies on additional resonant
hyperplanes, not merely the intended paired stratum. Files:
`overnight_uniform_pair_normal.*` and
`overnight_uniform_normal_symbolic.*`.

The new Laurent-DP evaluator scales every edge factor by `t^2`, so it can
handle both zero and nonzero apex placements. It first matched all 490
exact five-label star values and all 49 exact target values modulo1000003.
It then evaluated every one of the 258 independently inventoried seven-label
matching-deficient orbit columns at 180 generic paired base/normal choices.

| Seven-label data | Ordinary/augmented rank mod1000003 |
| --- | --- |
| `t^-3` coefficient | 8/8 |
| `t^-1` coefficient | 105/105 |
| All negative coefficients | 105/105 |
| `t^1` coefficient | 112/113 |
| All coefficients through `t^1` | 112/113 |

Thus the first regular coefficient restores the generic diagnostic gap at
seven labels, while principal parts alone do not distinguish the target
on these rows. The no-gap result is not an exact identity of rational
functions, and the positive gap is not by itself a characteristic-zero
certificate. Odd parity and agreement with the independently computed
first-residue rows were checked throughout.

At nine labels, the analogous proposed jet is `t^3`, following the possible
pattern `t^(N-6)`. The authorized bounded phase evaluated 100 paired
base/normal choices for all3,822 matching-deficient orbit columns. It took
242.5 seconds for the evaluations and247.2 seconds including rank checks,
using one core. The four nonzero coefficient blocks `t^-3,t^-1,t^1,t^3`
each have ranks100/100; all400 stacked rows are independent, ranks400/400.
This is underdetermined against the known generic dimension1970. It gives
neither rank stability nor a rejection of the jet pattern. Another100
points would cost roughly four minutes and would still supply at most800
rows, so this branch stops at that budget boundary.

Reproducible instruments and receipts:

- `overnight_uniform_paired_engine.cpp`, `overnight_uniform_paired_dp.py/json`:
  first-residue controls and seven-label gate;
- `overnight_uniform_principal_engine.cpp`, `overnight_uniform_principal.py/json`:
  all negative coefficients;
- `overnight_uniform_jet_engine.cpp`, `overnight_uniform_jet.py/json`:
  first regular seven-label coefficient;
- `overnight_uniform_jet9.py`, `overnight_uniform_jet9_100.json`:
  bounded nine-label phase, with source/point hashes and durable row output.

## Exact coefficient formula and next mathematical residual

For one rooted kernel, collect the zero base linear denominator factors as
`t d_1,...,t d_b`, and the nonzero ones as
`c_j(1+t rho_j)`. Set `k=N-4`, and let `h_s(rho)` be the complete homogeneous
symmetric polynomial, with `h_s=0` for negative `s`. The coefficient of
`t^ell` is exactly

```
(-1)^k / [(product d_i)(product c_j)]
  * sum_(j=0)^k binom(k,j) a_0^(k-j) a_1^j
      (-1)^(ell+b-j) h_(ell+b-j)(rho).
```

This follows by expanding the numerator and
`product(1+t rho_j)^(-1)=sum_s (-t)^s h_s(rho)`.
When `a_0=0`, only `j=k` remains; this makes the zero-apex vanishing order
above immediate. The target coefficient at `t^(2s-1)` is

```
(-1)^q / [(-2 sum p_i) product z_i^2]
    * h_s(p_1^2/z_1^2,...,p_q^2/z_q^2).
```

The live residual is to find a uniform linear combination of these
normal-dependent coefficients which annihilates every other-apex
contaminant while retaining the maximum. The first principal residue does
not do so. The seven-label diagnostic suggests that regular jets carry
information the singular part loses, but gives no uniform cancellation
identity.

Two related primary sources were read:
[Petrov, divided symmetrization](https://arxiv.org/html/1512.07136v2) and
[Amdeberhan, explicit divided-symmetrization computations](https://arxiv.org/html/1406.0447v1).
Their tree-edge difference denominators have useful degree and factor
cancellation rules. Our denominators are cut sums and shifted cut sums;
no valid change of variables preserving the full permutation action has
been established. Applying those theorems directly here would therefore
leave a missing bridge.
