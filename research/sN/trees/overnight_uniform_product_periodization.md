# Twisted periodization of the actual kernels

This is a linear operation on the rational kernels themselves, with every
apex placement retained. The leading near-integer version is **exactly
refuted at five labels**: one oriented star already gives twelve times the
maximum's entire leading normal coefficient. A bounded test of the complete
periodization also gives no separation, but that latter conclusion is only
numerical. This branch is therefore not being broadened.

## Definition and convergence

Write \(N=n+1\), distinguish frequency label \(0\), and take

\[
 \omega_0=1,\qquad \omega_i=z_i\ (i>0),\qquad \sum_{i>0}z_i=-1.
\]

For phases \(\theta_0=0\), define

\[
 \mathcal P_\theta R(z)=
 \sum_{\substack{k\in\mathbb Z^n\\\sum k_i=0}}
 e^{2\pi i\sum_{i>0}\theta_i k_i}
 R(1,z_1+k_1,\ldots,z_n+k_n). \tag{1}
\]

The frequencies are generic, avoiding the countably many translated poles
of the finite collection of kernels under consideration. We use only binary
phases, \(\theta_i\in\{0,1/2\}\), below.

The sum is absolutely convergent for every canonical tree kernel. If its
actual apex is label \(0\), rooted cut coordinates give independent sums of
terms \(1/[(Q+r)(Q+r+\varepsilon)]\), each absolutely summable.

Otherwise slice the sum by the actual apex frequency \(A=z_j+m\). In rooted
cut coordinates, fixing the distinguished coordinate imposes one integral
linear constraint on the cuts incident to that vertex. For generic offsets,

\[
 \sum_{r\in\mathbb Z}
 \frac1{|Q+r|\,|Q+r+\varepsilon A|}
 =O\!\left(\frac{\log(2+|m|)}{1+|m|}\right).
\]

This follows by separating the neighborhoods of the two poles and the tails.
If the distinguished vertex has degree at least two, ignoring its constraint
gives an upper bound. After multiplying by the numerator \(A^{n-3}\), the
layer is bounded by \(O(\log^{n-1}(2+|m|)/(1+|m|)^2)\).

If that vertex is a leaf, its incident cut is fixed rather than freely
summed. Its edge factor is \(1/(1+\varepsilon A)\), \(1/(1+A)\), or

\[
 1/[(1+A)(1+2A)],
\]

according to the cases below. The other \(n-2\) cuts are independent, and the
same summable bound follows. This special treatment matters: freely summing
that constrained cut can introduce poles absent from \(1\).

## The fixed-apex expression and the target

Put

\[
 g_z(t)=\sum_{m\in\mathbb Z}\frac{e^{2\pi i mt}}{z+m}
 =\frac{\pi e^{\pi i(1-2\{t\})z}}{\sin\pi z}
 \quad(t\notin\mathbb Z),
\]

with symmetric value \(g_z(0)=\pi\cot\pi z\). Although this individual
Fourier series is conditional, the differences used below are absolutely
convergent and continuous in \(t\).

For an actual apex at \(0\), the character on an edge cut is

\[
 \alpha_e=\theta_{\mathrm{child}}-\theta_{\mathrm{parent}}.
\]

Its factor in \(1\) is

\[
 \frac{1-e^{-2\pi i\varepsilon_e\alpha_e}}{\varepsilon_e}
 g_{Q_e}(\alpha_e).
\]

Untwisted periodization annihilates every fixed-apex unit. It also annihilates
the maximum, so it cannot separate them. For binary phases, a fixed-apex
unit vanishes unless every tree edge crosses the phase partition. On a
crossing edge its factor is \(2\pi\varepsilon_e\csc(\pi Q_e)\).

For \(B=\{i:\theta_i=1/2\}\), the normalized target product satisfies

\[
 \sum_{\sum k_i=0}\frac{(-1)^{\sum_{i\in B}k_i}}
                         {\prod_i(z_i+k_i)}
 =-\frac{2\pi^{n-1}\sin(\pi\sum_{i\in B}z_i)}
          {\prod_i\sin(\pi z_i)}. \tag{2}
\]

To prove (2), multiply the Fourier series \(g_{z_i}(t+\theta_i)\) and take
its constant coefficient. The total frequency is \(-1\); splitting the
integral at \(t=1/2\) gives the displayed expression. Absolute convergence
of the constrained convolution justifies the coefficient calculation.
For odd \(N\), the maximum kernel at \(\omega_0=1\) is precisely the product
on the left. Binary twisting therefore preserves a nonzero target.

## Explicit other-apex terms

Now let the actual apex be \(j\ne0\), and root its nonapex tree at \(r\).
Write \(A=z_j+m\), \(Q_e\) for its unshifted rooted cuts, and

\[
 \beta=\theta_j-\theta_r,\qquad
 \alpha_e=\theta_{\mathrm{child}}-\theta_{\mathrm{parent}}.
\]

Let \(s_e=1\) if the distinguished vertex is the child of \(e\), \(s_e=-1\)
if it is the parent, and \(s_e=0\) otherwise; let \(b=1\) when it is the root,
and \(b=0\) otherwise. The cut shifts obey \(\sum_e s_e k_e=bm\).
If the distinguished vertex has degree at least two, its contribution is

\[
 \int_0^1\sum_{m\in\mathbb Z}
 e^{2\pi i(\beta-bt)m}(-A)^{n-3}
 \prod_e\frac{g_{Q_e}(\alpha_e+s_et)
             -g_{Q_e+\varepsilon_e A}(\alpha_e+s_et)}
                  {\varepsilon_e A}\,dt. \tag{3}
\]

This formula keeps the missing apex terms explicitly. In particular, a
same-phase free edge gives the generally nonzero cotangent difference

\[
 \frac{\pi}{\varepsilon A}
 [\cot\pi Q-\cot\pi(Q+\varepsilon z_j)].
\]

Thus the fixed-apex proper-coloring support statement cannot be applied to
the complete periodization.

Formula (3) is also a finite closed calculation. Expand the edge differences
by bits \(\delta_e\). On each phase interval, write

\[
 \{\alpha_e+s_et\}=o_e+s_et,\quad
 \gamma(t)=\beta-bt-\sum_e\delta_e\varepsilon_e(o_e+s_et).
\]

The remaining apex sum is

\[
 \sum_m\frac{e^{2\pi i\gamma m}}{(z_j+m)^2}
 =2\pi i\,g_{z_j}(\gamma)
       \left(\{\gamma\}+\frac1{e^{2\pi iz_j}-1}\right).
\]

Split at \(0,1/2,1\) and at the finitely many crossings \(\gamma(t)\in\mathbb Z\).
The frequency relation cancels the other \(t\)-dependence, leaving an
exponential \(e^{-2\pi it}\) times a linear polynomial. Its elementary
antiderivative supplies the evaluator without any lattice truncation.

For a distinguished leaf, omit its incident edge \(e\) from the product.
Let \(\beta'=\beta\) for a nonroot leaf and
\(\beta'=\beta-\alpha_e\) for a root leaf. The exact answer is

\[
 (-1)^{n-3}\!\prod_{f\ne e}\varepsilon_f
 \sum_{\delta\in\{0,1\}^{n-2}}(-1)^{|\delta|}
 \prod_{f\ne e}g_{Q_f+\delta_f\varepsilon_f z_j}(\alpha_f)
 H\!\left(z_j,\beta'-\sum_{f\ne e}\delta_f\varepsilon_f\{\alpha_f\}\right),
\]

where

\[
\begin{array}{ll}
H(z,t)=g_z(t)-g_{z+\varepsilon_e}(t),&\text{nonroot leaf},\\
H(z,t)=g_z(t)-g_{z+1}(t),&\text{root leaf, }\varepsilon_e=1,\\
H(z,t)=g_z(t)+g_{z+1}(t)-2g_{z+1/2}(t),&\text{root leaf, }\varepsilon_e=-1.
\end{array}
\]

The last line retains the exceptional half-integer pole. These formulas
follow from the partial fractions of \(1/[A(1+\varepsilon A)]\) and
\(1/[A(1+A)(1+2A)]\), respectively.

## Near-integer leading coefficient: a finite exact obstruction

Take \(\omega=(1,k_1+tp_1,\ldots,k_n+tp_n)\), with integer
\(\sum k_i=-1\), normal \(\sum p_i=0\), and affine-lattice weight
\((-1)^{\sum_{i\in B}k_i}\). The maximal pole order of a canonical kernel
is \(n-1\). Its coefficient comes from only the following finite states:

* Nonzero integer actual apex: every cut is at \(0\) or
  \(-\varepsilon_e A\). Reconstructing the distinguished coordinate \(1\)
  forces \(A=1\) or \(A=-1\).
* Zero actual apex: exactly one cut is a nonzero integer; its edge meets the
  distinguished vertex and its value is \(1\) or \(-1\).

All critical integer frequencies have absolute value at most \(n\). For a
nonzero actual apex there is at most one vanishing factor per edge. For zero
actual apex, at least one cut is nonzero because a coordinate is fixed at 1;
the numerator contributes order \(n-3\). These facts prove the classification.
The convergence estimates above, with the nearest-pole terms included,
give a summable uniform majorant after multiplication by \(t^{n-1}\), so
the leading coefficient may be taken termwise.

At \(N=5\), \(B=\{1,2\}\), the target leading coefficient is

\[
 2(p_1+p_2)/(p_1p_2p_3p_4).
\]

For the full permutation sum of the canonical star

\[
 U=\sigma(x_1-x_0+\sigma(x_2-x_1)+\sigma(x_3-x_2)+\sigma(x_4-x_2)),
\]

the entire leading coefficient is **twelve times this target**, as a rational
identity in the normal. The independent checker enumerates the integer box
\([-4,4]^4\), all 120 label permutations, and finds 720 critical states. It
uses normalized heads, then proves the identity over
\(\mathbb Q(r,s)\), with \(p=(1,r,s,-1-r-s)\), by a zero polynomial numerator.
Consequently every linear postprocessing of this whole leading normal curve
fails to separate the maximum from stars.

The exact ten-star evaluation gate has ranks 4/4 on 40 normals. The whole
complete-periodization test, using (3) and the leaf formulas, gives numerical
ranks 4/4 on 14 generic complex frequency choices. The same star appears to be
twelve times the target there as well, but this **complete-periodization
identity is not symbolically certified**. The numerical evaluator checks
the exact three-label maximum identity and the independently proved
five-label identity \(F_{\mathrm{star}}=3F_{\mathrm{path}}\); the largest
relative control discrepancy is \(1.5\cdot10^{-12}\).

Files: `overnight_uniform_product_integer_gate*` (exact finite producer),
`overnight_uniform_product_integer_check*` (independent symbolic check), and
`overnight_uniform_product_periodic_numeric*` (bounded numerical diagnostic).
No Hilbert-series lift, unproved valuation extension, or matching vanishing
is assumed in these calculations.
