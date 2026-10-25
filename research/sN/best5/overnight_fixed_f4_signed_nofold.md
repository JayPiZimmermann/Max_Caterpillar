# The signed six-term state is not a shallow fold

The nonnegative function from `overnight_fixed_f4_cone.md`,

\[
 F=B+\sum_{i=1}^4D_i-q,
\]

cannot equal \(\sigma(g)\) for any finite shallow preactivation \(g\),
even with arbitrary first hidden layer directions and biases. This closes
the arbitrary-direction question left open in that frozen note. It does
not classify all nonnegative signed states in the 48-function span.

Here \(S=\sum_i x_i\),
\(q=\sigma(\min_i x_i)\),
\(B=\sigma(\min_i(S/2-x_i))\), and
\(D_i=\sigma(\min\{S/2,x_i+x_j-S/2:j\ne i\})\).

## Which hyperplanes can lie in the zero set?

**Lemma.** If a linear hyperplane \(H\) is contained in \(\{F=0\}\), then
it is one of the four hyperplanes

\[
 S=0,\qquad x_i+x_j=x_k+x_l
\]

corresponding to the three partitions into two pairs.

Suppose \(H\ne\{S=0\}\), and let \(V=H\cap\{S=0\}\), a two-dimensional
subspace. Choose \(y\in H\) with \(S(y)>0\). If some \(w\in V\) has
\(\max_i w_i+\min_i w_i>0\), choose a maximal coordinate \(i\).
Every \(w_i+w_j\), \(j\ne i\), is strictly positive. For small
\(\varepsilon>0\), the term \(D_i(w+\varepsilon y)\) is therefore exactly
\(\varepsilon S(y)/2>0\). Since \(w\) has a strictly negative coordinate,
\(q(w+\varepsilon y)=0\), giving \(F(w+\varepsilon y)>0\), a contradiction.
Applying the same argument to \(-w\) proves

\[
 \max_i w_i+\min_i w_i=0\qquad(w\in V).
\]

On \(S=0\), this condition says that the four coordinates can be paired
into two opposite pairs. Its zero set is the union of three linear
planes. A linear subspace over the real numbers cannot be a finite union
of proper linear subspaces. Thus \(V\) equals one of these planes, and,
after relabeling, a normal of \(H\) has the form \((a,a,b,b)\).

If \(a=b\), then \(H=\{S=0\}\). If \(a=-b\), it is the stated
pair-balance hyperplane. In all other cases choose pair sums \(P,Q\)
with \(aP+bQ=0\) and \(P+Q>0\); this is possible because \(a\ne b\).
Also \(P\ne Q\), because \(a+b\ne0\). Exchange the pairs if necessary
so \(P>(P+Q)/2\). The point

\[
 x=(L,P-L,Q/2,Q/2)
\]

belongs to \(H\). For sufficiently large \(L\), it has \(q(x)=0\), while

\[
 D_1(x)=\min\{(P+Q)/2,\ P-(P+Q)/2,\ L-P/2\}>0.
\]

This is again a contradiction, proving the necessary classification.

## Eliminating all foreign first hidden layer walls

Suppose \(\sigma(g)=F\), and consolidate proportional walls in the
homogeneous shallow function \(g\). On the open set \(\{F>0\}\),
\(g=F\). If a non-F4 wall of \(g\) intersects this open set, a generic
point on that wall gives a nonzero shallow gradient jump where \(F\) is
linear, which is impossible. Thus a surviving non-F4 wall would have to
lie entirely in \(\{F=0\}\). The lemma says every such wall is already an
F4 wall. Consequently \(g\) lies globally in the span of coordinates and
the absolute values of the 24 F4 normals.

## Seven exact evaluations finish the proof

Every function in that shallow span satisfies

\[
\begin{aligned}
 g(-1,-1,3,1)={}&-g(0,0,1,1)-g(0,-1,0,1)+g(0,-1,2,1)\\
 &-g(-1,0,0,1)+g(-1,0,2,1)+g(-1,-1,0,2).
\end{aligned}
\]

The target \(F\) is zero at the six points on the right and one at the
point on the left. All six zero points belong to the closure of
\(\{F>0\}\): changing their fourth coordinate by
\(+\varepsilon,+\varepsilon,-\varepsilon,+\varepsilon,-\varepsilon,
+\varepsilon\), respectively, gives directional derivative \(1/2\).
Hence continuity forces \(g=0\) at the six points, while \(g=1\) at the
left point, contradicting the identity.

A biased shallow representation reduces to a homogeneous one by taking
its recession function. The standard-library checker
`overnight_fixed_f4_signed_nofold_verify.py` verifies the 28 feature
identities, the seven target values, and the six exact positive directional
derivatives without reading any producer artifacts or using a solver.
The hyperplane classification is the analytic bridge above; no Lean
formalization is claimed.
