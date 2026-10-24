# Complete paired-cut residue and a clean pendant-pair operation

25 October 2026. General termwise identities, with exact controls and an
independent semantic review. These are operations on the actual rational
functions, not assignments guessed from their tree descriptions. They do
not yet give a separator with nonzero response on the maximum.

Use the canonical full-hinge tree kernel and unaveraged permutation sum

```
R_U(omega) = (-a)^(N-4) product_e 1/[q_e(q_e+epsilon_e a)],
F_U(omega) = sum_(pi in S_N) R_U(omega_pi).
```

Here the tree has `N-1` nonapex vertices, `r` is its head root, `a` is its
apex frequency, and the root-away cut sum and edge sign are `q_e` and
`epsilon_e`. The sign is positive when the positive endpoint lies away
from the root. Assume odd `N>=5`.

Set the frequencies to `(z,-z-S,xi_1,...,xi_(N-2))`, with `sum xi=S`.
Take the residue at `S=0`, and write `eta=xi|_(S=0)`, so `sum eta=0`.
All assertions first hold for generic independent `eta` subject to this
single relation, and then as rational identities. Avoid additional proper
subset-sum zeroes and the other denominator hyperplanes. Every contributing
individual summand has a simple `S` pole.

## The outlier-apex terms are smaller marked kernels

Suppose one outlier is the actual apex and the other is a tree leaf `v`,
whose neighbor is `h`. Delete `v`, retaining the old head root unless `v=r`,
in which case reroot at `h`. Call the smaller canonical unit `V`.

Let `A_(V,h)(z;eta)` be the sum over all assignments of the `eta` frequencies
to the nonapex vertices of `V`, with apex frequency `z` and the frequency
assigned to `h` reduced by `z`. Thus each smaller kernel has total frequency
zero. The two outlier placements give

```
-c_v [A_(V,h)(z;eta) + A_(V,h)(-z;eta)],                (1)
```

where

- if `v!=r`, then `c_v=1` when the positive endpoint of its edge is `v`,
  and `c_v=0` otherwise;
- if `v=r`, then `c_v=epsilon_(r,h)`.

For a nonroot leaf the relevant cut factor is
`(-z-S)(-S)` and its residue is `1/z`; the ratio of the two kernel
prefactors is `-z`, giving coefficient `-1`. For a root leaf, the
factor is `S(S+epsilon z)`, giving coefficient `-epsilon` after the same
prefactor ratio. Absorbing the removed leaf's frequency into its hub makes
every remaining cut sum agree with the corresponding smaller kernel.
This proves (1), including both possible root-leaf orientations.

Every denominator in (1), as a function of `z`, has constant term a sum
of a subset of the `eta` frequencies and `z` coefficient in
`{0,+1,-1,+2,-2}`. Its nonconstant poles therefore lie at signed subset
sums or signed half-subset sums.

## The finite-apex terms delete a pendant pair

The two outliers must occupy a two-vertex component `C` left by deleting
one tree edge. Write `h` for the vertex outside `C` incident to that edge,
and `b` for its endpoint in `C`. Delete `C`; retain `r` if it lies outside
`C`, and otherwise reroot at `h`. Call the resulting canonical unit `V`.
Its arity is `N-2`. For every assignment of the remaining `eta` frequencies
to its apex and tree vertices, multiply `R_V` by the following weight,
where `a` is its assigned apex frequency.

| Position of the head root | Condition | Weight |
|---|---|---|
| Outside `C` | Boundary sign `epsilon`, either value | `-2 epsilon a/(z^2-a^2)` |
| Inside `C`, at `b` | Boundary sign `+` | `-2a/(z^2-a^2)` |
| Inside `C`, at its pendant leaf | Boundary sign `+`, internal sign `+` | `-2a/(z^2-a^2)` |
| Inside `C`, at its pendant leaf | Boundary sign `+`, internal sign `-` | `-2a(z^2+2a^2)/[(z^2-a^2)(z^2-4a^2)]` |
| Inside `C` | Boundary sign `-` | Zero |

The weight already sums the two assignments of the outliers to `C`.
No further factor of two is present.

To verify the table, the boundary cut is `q=-S` when the root is outside
`C`. Its residue and the prefactor ratio give `-epsilon a`. If the root
is inside `C`, the cut is `q=S-a`; only sign `+` has a pole and its factor
is `-a`. If the root is outside `C` or is its boundary hub, the internal
cut is `q=+z` or `-z`, whose two terms sum to `2/(z^2-a^2)` for either
internal sign. If the root is its pendant leaf, the internal cut is
`q=+z-a` or `-z-a`. Sign `+` gives the same sum, whereas sign `-` gives

```
2(z^2+2a^2)/[(z^2-a^2)(z^2-4a^2)].                    (2)
```

Summing (1) over eligible leaves and the table over eligible pendant pairs
is the full cut residue. There are no omitted apex placements.

## A clean operation that mirrors deletion of a matched pair

Fix one frequency `eta_i`. Then

```
Res_(z=2 eta_i) Res_(S=0) F_U(z,-z-S,xi)              (3)
```

is zero unless all four conditions hold:

1. The head root `r` is a leaf.
2. Its neighbor `b` has degree two.
3. The positive endpoint of `(r,b)` is `r`.
4. If `h` is the other neighbor of `b`, the positive endpoint of `(b,h)`
   is `h`.

Equivalently the pendant two-edge path from the head has root-relative
signs `(-,+)`. In this case (3) is minus the fixed-apex sum of the lower
canonical unit obtained by deleting `r,b` and rerooting at `h`: the apex
frequency is `eta_i`, and the other `N-3` frequencies are assigned to the
remaining tree vertices in all `(N-3)!` ways.

Indeed, the exceptional entry of the table is

```
2a/(z^2-a^2) - 4a/(z^2-4a^2),                        (4)
```

whose residue at `z=2a` is `-1`. Genericity excludes `2 eta_i` from the
poles of all other finite-apex assignments and from every signed subset
sum or signed half-subset sum in the outlier-apex terms. These exclusions
are nonempty on `sum eta=0`: no proper nonempty subset-sum linear form is
identically `2 eta_i` or `4 eta_i` there when `N-2>=3`. Also exclude
`eta_i=0` and coincidences with the signed individual frequencies.

This operation has two exact structural properties:

- If the original even tree has no perfect matching, neither does the
  lower even tree: a matching of the latter together with edge `(r,b)`
  would match the original tree.
- It maps the maximum's kernel to zero, because that kernel has no generic
  `S=0` pole.

Thus (3) is a legitimate uniform relation constraint and a clean pruning
operation. The second property prevents using it alone as a lower-bound
separator. A nonzero target response still has to come from a compatible
regular part or another operator.

## Verification and exact remaining gap

`overnight_uniform_pruning_residue_recurrence.py/.json/.log` compares the
recurrence with normalized-head direct permutation residues for every one
of the26 five-label root/orientation orbits and four seven-label units.
All30 cases pass in0.5 seconds.

`overnight_uniform_pruning_double_residue.py/.json/.log` directly checks
(3) on those26 five-label orbits, three seven-label units, and a nine-label
subdivided claw with arm lengths1,3,3 and the head at an eligible pendant
path. All30 cases pass in12.3 seconds. The nine-label tree has no perfect
matching; deleting the detected pair leaves the smaller nonmatchable tree.

The independent fixed-layer proof agent checked the finite-apex factor
table, the coefficient and sign in (4), the fixed-apex multiplicity, the
outlier-apex pole exclusion, and the genericity quantifiers. This is a
semantic audit of the general identity; it does not substitute the finite
controls for a proof.

The recurrence still has two kinds of marked data: apex-dependent weights
on the lower finite-apex kernels, and an external apex with a shifted hub
in (1). Replacing either by the unmarked permutation sum loses information.
The clean pole (3) removes the latter contribution but also kills the target.
A uniform separator needs a generating-function operation that retains a
nonzero maximum response while controlling both sorts of marked data.
