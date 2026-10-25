# Only the exceptional-root coface needs filling

This is a uniform simplification of the **actual coherent simplex lift**.
It removes the sum over all cofaces from each undoubled filling step.
It does not yet bound the total number of cubes exponentially.

Use the star-Koszul contraction $H$, root $0$, and root-cycle generators

\[
 z_{ij}=E_{ij}-g_j^{-1}E_i+g_j^{-1}E_j
 \qquad(i>j>0).
\]

Here $g_i$ is translation by $e_i-e_0$, $E_i=E_{i0}$, and
$dE_{ij}=g_i/g_j-1$. Let $\phi_s$ be the order-preserving coface omitting
label $s$, so $\delta=\sum_s(-1)^s\phi_s$.

## Root-preserving naturality

For every $s>0$,

\[
 H\phi_s=\phi_s H.
\]

Indeed the change to the star/$z$ basis commutes with an order-preserving
label injection fixing $0$. In the tensor contraction, inserting a zero
coordinate inserts no summand, and the order of all existing coordinates
is preserved. Its prefix augmentations and first-star cutoff are therefore
unchanged. The inverse basis change is natural for the same reason.

Every lift produced by $H$ lies in $\ker H$, since $H^2=0$. The canonical
closed correction $C$ used in the undoubled recurrence also lies in
$\ker H$: in the star/$z$ basis it has constant coefficients and only $z$
factors. Thus $H(X-C)=0$, and every $s>0$ term vanishes individually:

\[
 \boxed{H\delta(X-C)=H\phi_0(X-C).}
 \tag{1}
\]

The complete alternating boundary still supplies the boundary of the
resulting chain. Equation (1) only removes terms from the filling
calculation; it does not discard geometric facets.

Exact original-cube controls use the actual corrected simplex lifts in
dimensions three, four and five. Their corrected supports are 23, 276 and
4965 cubes; (1) gives precisely the full next lifts of 134, 3150 and 102187
cubes. Every omitted coface is checked separately.

## A six-square root-transfer correction

Put $I=i+1$, $J=j+1$. The only exceptional coface changes the root from $0$
to $1$. Direct substitution gives

\[
 \phi_0(z_{ij})
 =z_{IJ}-\frac{g_1}{g_J}z_{I1}
             +\frac{g_1}{g_J}z_{J1}.
\]

Its constant homology representative and a primitive for the difference are

\[
 b_{ij}=z_{IJ}-z_{I1}+z_{J1},\qquad
 P_{ij}=E_{1J}(-z_{I1}+z_{J1}),
\]

so that

\[
 \phi_0(z_{ij})-b_{ij}=dP_{ij}.
 \tag{2}
\]

The identity uses $dE_{1J}=g_1/g_J-1$ and $dz=0$. It is also checked
directly after expanding into original translated cubes.

For a product of $k$ closed generators, let $f_i=\phi_0(z_i)$ and
$b_i=b(z_i)$. The telescoping primitive is

\[
 \phi_0(z_1\cdots z_k)-b_1\cdots b_k
 =
 d\left[
 \sum_{i=1}^k(-1)^{i-1}
 f_1\cdots f_{i-1}P_i b_{i+1}\cdots b_k
 \right].
 \tag{3}
\]

An $f_i$ has three original segments, a $b_i$ has at most nine, and a
$P_i$ at most six squares. Before cancellation the primitive has at most

\[
 6\sum_{i=1}^k3^{i-1}9^{k-i}=9^k-3^k
\]

cubes. This applies to one entire closed-wedge transfer, without first
expanding each old cube through another arbitrary filling.

## Remaining quantitative question

Writing $A=H\phi_0$, the actual recurrence is now
$X_n=A(X_{n-1}-C_{n-1})$, with its scalar normalizations understood.
The remaining work is to control the closed corrections and the powers of
$A$ on their geometric lifts. A polynomial number of choices at every
arity can still accumulate factorial support; the one-transfer estimate
above alone does not prevent this.

There is a further exact localization. Since $H\phi_1H=0$,

\[
 A^2=H(\phi_0-\phi_1)A,
 \qquad A|_{\ker H}=H(\phi_0-\phi_1)|_{\ker H}.
\]

The two cofaces agree on every vector not involving the old root label.
Their difference therefore vanishes on a cube whose head and all
generators have zero coordinate at that root. This suggests controlling
the root incidence of whole closed-cycle blocks; such a control has not
been proved for the required corrections.

## Geometric aggregation, retaining the face corrections

The formal contraction subdivides a long segment into unit translates.
These can be joined geometrically, but the support functions require
internal-face corrections. For fixed remaining generators $L$ and
collinear base cells with coordinate intervals $[a,b]$, write

\[
 U_{[a,b]}=
 h_{\operatorname{conv}(0,h+[a,b]v+\sum_{\ell\in L}[0,\ell])}.
\]

When the base affine hull avoids the apex,
$U_{[a,b]}+U_{[b,c]}=U_{[a,c]}+U_{\{b\}}$.
More generally, if an original and compressed signed collection of
intervals have the same weighted interior indicator, their support
function difference is

\[
 \sum_t
   (\text{original ending weight at }t
     -\text{compressed ending weight at }t)\,U_{\{t\}}.
\]

This follows by splitting both collections at every endpoint. The
coefficient records the removed internal faces. Every lower-dimensional
term is retained, and the same aggregation can be applied to it.

The actual ordered-lift controls give:

| Simplex dimension | Formal cubes | Nondegenerate top pyramids | Merged top pyramids | All retained dimensions |
|---:|---:|---:|---:|---:|
| 3 | 3 | 1 | 1 | 1 |
| 4 | 134 | 61 | 53 | 61 |
| 5 | 3150 | 1424 | 1198 | 1423 |
| 6 | 102187 | 41774 | 34258 | 41688 |

The largest resulting generator lengths are 1, 2, 4, and 7. Thus this
ordinary axis aggregation reduces the top count, but barely changes the
total count after retaining face corrections. It is not evidence of a
uniform exponential construction. Initial pruning removes dependent or
zero-height cones only in the top quotient, so these counts do not state
an exact maximum network.

The producer checks each interval identity algebraically through its
endpoint data, and uses seven exact integer evaluations per arity as
additional support-function convention controls. Those evaluations
alone would not certify an identity.

An optional raw-power campaign reached $A^4X_3$ with 239146 formal cubes
and $A^4z_{21}$ with 22179. It then hit the declared 3 GiB memory bound
while expanding $A^5z_{21}$, and exited with code 1. This is a resource
stop, not a mathematical obstruction or a completed asymptotic test;
its durable log and exit receipt are retained.

Producers and receipts:
`overnight_upper_ordered_single_facet.py/.json` and
`overnight_upper_ordered_root_transfer.py/.json`.
They preserve all earlier frozen artifacts. None of these results is Lean
verified.
