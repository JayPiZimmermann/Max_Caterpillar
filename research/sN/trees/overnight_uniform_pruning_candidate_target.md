# Exact necessary maximum response of the sparse signed-root score

This is a combinatorial calculation using the proved signed caterpillar
identity. It does not prove that the score descends to a linear functional
on rational kernels. It shows that, if it did descend, its response on the
maximum would be nonzero at every odd arity `N>=5`.

For a canonical tree unit, use the notation of the pruning note and the
following fixed score, whose finite five- and seven-label gates passed:

```
Q_* = (15/8)[36 D_1 - 2 K_1 + 2 epsilon D_1
            - 6 K_1^chi - 2 epsilon D_1^chi - 3 epsilon D_2],
D_j = sum_(v,w) dist(v,w)^j I_v I_w,
K_j = sum_(v,w) dist(v,w)^j (kappa_v+kappa_w) I_v I_w.
```

The superscript `chi` inserts the bipartite factor `chi_v chi_w`.
All sums use ordered pairs. The score vanishes on every tree without a
perfect matching because every signed rooted extension count `I_v` does.

Put `N=2q+1`. In the standard caterpillar construction, a cut set contributes
a perfectly matchable tree exactly when it contains every even position
`2,4,...,2q-2`; its odd positions are arbitrary. To see this, the first
vertex must pair with the next vertex, whether that next vertex is a spine
vertex or a leaf. A second leaf at the same first spine vertex prevents a
matching, so the next pair begins at a new spine vertex. Repeating gives
the characterization. Equivalently forced leaf-pair removal gives this
induction from the other end. Thus the only nonzero scores lie on a Boolean
cube of `2^q` cut descriptions.

Let `b_j` indicate that the odd cut in pair `j` is present. Pair `j` contains
vertices `a_j=2j-1` and `c_j=2j`. If `b_j=0`, the latter is the former's
leaf; if `b_j=1`, both are spine vertices. The unique perfect matching
pairs these vertices, and contracting it gives a path on `q` vertices.
Write

```
C_j = binom(q-1,j-1),
s_j = (-1)^(b_1+...+b_(j-1)),
I_(a_j)=s_j C_j,       I_(c_j)=-s_j C_j,
chi_(a_j) I_(a_j) = chi_(c_j) I_(c_j) = (-1)^(j-1) C_j,
kappa_(a_j)=2-b_j,     kappa_(c_j)=b_j.
```

The sign formula follows by ordering the matched dominoes in any extension
of the contracted path; interchanging two blocks is an even permutation.
The sign of the caterpillar's coefficient is precisely
`epsilon=(-1)^(q-sum b_j)`.

For `j<k`, distances between the two pairs have the form

```
d((j,s),(k,t)) = (k-j)+sum_(l=j)^(k-1) b_l
                 +s(1-2b_j)+t,        s,t in {0,1}.
```

Let `E` denote uniform averaging over the Boolean cube and put

```
B = binom(2q-2,q-1),
A = binom(2q-2,q-2),
B_0 = binom(2q-4,q-2).
```

Expanding the preceding distance formula gives

```
E D_1 = -2B,
E D_2 = -2B+4A,
E D_1^chi = -12B_0,
E(epsilon D_1)=E(epsilon K_1)=0,
E(epsilon K_1^chi)=0                    for q>=3.
```

Here the `K_1` cross-pair term always omits at least one endpoint bit, so
its top Boolean coefficient is zero. The `K_1^chi` expression has Boolean
degree at most two. For `D_1^chi`, the cumulative alternating binomial
identity `sum_(j<=k)(-1)^(j-1)C_j=(-1)^(k-1)binom(q-2,k-1)` and the tree
cut formula for quadratic distance sums give the displayed `B_0` term.

Consequently the signed score sum over the construction is, for `q>=3`,

```
S_q = (15/8) 2^q [2B-12A+24B_0]
    = -15 * 2^(q-2) * binom(2q-2,q-1)
      * (4q^2-21q+18)/[q(2q-3)].
```

The necessary maximum response is `S_q/(2q+1)!`. It never vanishes:
the quadratic has discriminant153, which is not a square. At `q=2` the
small cube gives response1 directly. Examples are

| `N` | Necessary response |
|---|---|
| 5 | 1 |
| 7 | 1/28 |
| 9 | 1/3024 |
| 11 | -13/166320 |
| 13 | -1/154440 |

`overnight_uniform_pruning_candidate_target.py/.json/.log` checks the
unreduced alternating sum through13 labels. It obtains signed rooted
counts from forced perfect matching and the contracted-tree hook formula,
without Fourier sampling. This check does not address the remaining issue:
whether this score respects every rational-kernel relation at arbitrary
arity. Its nonzero necessary target value cannot replace that requirement.
