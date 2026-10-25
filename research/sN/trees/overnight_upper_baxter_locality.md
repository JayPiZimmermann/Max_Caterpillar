# A classwise Baxter bridge needs apex attachments

The natural omitted-apex union-of-twin-trees bridge fails already on the
smallest nontrivial class, even with arbitrary real heads, inner weights,
output coefficients, and width. This is a locality obstruction to that
specific classwise realization, not to all Baxter-based constructions.

The two nonapex words

\[
 (3,1,4,2),\qquad(3,4,1,2)
\]

have the same forward and reverse binary-search-tree pair. The undirected
union graph is the four-cycle

\[
 G=\{12,13,24,34\}.
\]

The characterization of twin classes by the linear extensions of the
union with the second orientation reversed is standard; see
[Chatel–Pilaud, Section 2.1](https://arxiv.org/html/1411.3704#S2.SS1).
Only that combinatorial indexing is used here. The obstruction below is
an independent calculation for the original signed caterpillar functions.

Let $F$ be their unaveraged signed word sum at five inputs, with common
apex $0$. Apply $D_{-e_2}$ and $D_{-e_3}$ and retain the remaining labels
$\{0,1,4\}$. For a second-hidden-layer unit with comparisons contained in
$G$, every surviving inner comparison has been frozen: $G$ has no edge
on those three labels. A zero outer preactivation therefore leaves only
a ReLU of a linear function. Positive outer preactivations give shallow
functions, and negative ones give zero. This argument permits arbitrary
real inner weights and arbitrary linear heads.

Consequently the iterated derivative of every such unit lies in $L_1$.
The same is true of any $L_3$ error after two directional reductions.
Every homogeneous shallow function $g$ has linear odd part
$g(x)-g(-x)$. Hence the functional

\[
 \mathcal E(g)=
 [g(x+y)-g(-x-y)]-[g(x)-g(-x)]-[g(y)-g(-y)]
\]

vanishes on these iterated derivatives, for $x=e_1$, $y=e_4$.
The class target instead gives

\[
 \mathcal E(D_{-e_3}D_{-e_2}F)=-4.
\]

The reversed deletion order gives the same value. The standard-library
checker rebuilds the raw word functions, takes the derivatives directly,
and never uses Fourier kernels, normalized heads, or a rank calculation.

The same control gives a nonzero defect for every nonapex pair:

| Remaining nonapex pair | Defect |
|---|---:|
| 12 | -2 |
| 13 | -6 |
| 14 | -4 |
| 23 | -2 |
| 24 | -2 |
| 34 | -4 |

Thus any single fixed comparison graph omitting the apex and representing
this entire class would have to contain all six nonapex comparisons.
Adding only the incomparable pair $14$ still misses the required pair $23$.
An apex attachment is a genuine change of model: adding all apex comparisons
makes every tied set containing the apex connected.

Before the locality proof was found, the canonical union-cycle face family
gave an exact finite rank obstruction, 144 versus 145 on 176 columns, with
all 32 independent rational kernel relations checked. Adding the local
swap head $\pm(e_1-e_4)$ gave a modular diagnostic gap on 328 columns.
The all-real locality proof now subsumes both proposed repairs for this
fixed graph; the latter diagnostic does not need promotion to a certificate.

Sources and receipts:
`overnight_upper_baxter_locality.py/.json`,
`overnight_upper_baxter_union.py/.json`,
`overnight_upper_baxter_union_exact.py/.json`.
The failed first locality run was a Python empty-child indexing error;
the corrected producer completed with exit zero in the `baxter_locality2`
log. No mathematical conclusion uses the failed run.
