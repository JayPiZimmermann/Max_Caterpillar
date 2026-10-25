# Dictionary sufficiency: simplification without changing the proof structure

Date: 2026-10-25. The three steps remain: remove a lower-dimensional
error using faces, reconstruct from opposite-face differences, and prove
those differences by the direction classification and arity induction.

## Direct replacement: finite face elimination

Let \(V\) be a linear space of support-function combinations, stable under
every directional germ \(\partial_u\). Let \(S\) be a polytope whose proper
face support functions lie in \(V\). Suppose
\[
 g=a h_S+v\in L_k,\qquad a\ne0,\quad v\in V,\quad k<\dim S.
\]
Then \(h_S\in V\).

Write \(g=\sum_{i=1}^m c_i h_{P_i}\) with \(\dim P_i\le k\).
For each \(i\), choose a direction \(u_i\) orthogonal to
\(\operatorname{dir}P_i\) but not to \(\operatorname{dir}S\), and set
\(A_i=I-\partial_{u_i}\). Such a direction exists because the latter
direction space has strictly larger dimension: project a vector of
\(\operatorname{dir}S\setminus\operatorname{dir}P_i\) onto
\((\operatorname{dir}P_i)^\perp\).

For every polytope \(P_i\), every partial composition of the \(A_j\)
sends \(h_{P_i}\) to a linear combination of support functions of faces
of \(P_i\). The factor \(A_i\) kills all such functions: \(u_i\) is
constant on each face, so its germ is the function itself. Subsequent
factors preserve zero. Consequently
\[
 A_m\cdots A_1g=0.
\]
On the other hand, \(A_i\) preserves \(V\), and
\(A_i h_S-h_S=-h_{S^{u_i}}\in V\), since the exposed face is proper.
Thus the displayed zero is congruent to \(a h_S\) modulo \(V\), proving
the claim.

This replaces the dimension-by-dimension peeling scheme, its recursively
chosen direction sets, the simultaneous avoidance of other maximal
direction spaces, and the two-part residual invariant. It preserves the
outer induction on simplex faces and all theorem conclusions.

### Checks of the replacement

- No commutativity is asserted or required. Each original summand is
  followed through its descendants until its own annihilating factor.
- Translations do not cause an error. If \(u\) is constant on an affine
  polytope \(P\), then \(P^u=P\), hence \(\partial_u h_P=h_P\), even
  when the constant value is nonzero.
- A face of a face is a face of the original polytope. Subtraction only
  introduces linear combinations, so the descendant argument applies to
  signed coefficients as well.
- The dictionary span is germ-stable: derivatives of its polytope-face
  generators are further faces; derivatives of a coordinate or
  coordinate-difference ReLU are itself, zero, or its linear argument.
  The dictionary contains the required linear functions.
- The empty low-dimensional expression gives \(g=0\) and the conclusion
  immediately. A zero-dimensional \(P_i\) is killed by every factor.
- The directions must avoid \(\operatorname{dir}S\); arbitrary directions
  would risk leaving the full simplex unchanged and invalidate the outer
  induction.

For the paper use \(V=\operatorname{span}\mathcal D\),
\(S=\Delta_T\), and the error produced by the existing coordinate-vertex
deletions. Its coefficient \(a=(-1)^{N-|T|+1}\) is nonzero, and its
dimension bound is \(|T|-2<\dim\Delta_T=|T|-1\).

The same mechanism gives the stronger abstract statement
\[
 F\operatorname{Span}(\mathcal F)\cap L_d
 \subseteq G\operatorname{SpanRel}(\mathcal F,U),\qquad d<\dim U,
\]
for a face-closed family \(\mathcal F\). Every admissible germ belongs to
the relative face span, so each factor changes the current residual by a
member of that span. No extra linear remainder is required. The new Lean
helper [Annihilate.lean](../../../MaxNN/Constructions/Paramid/Geom/Faces/Annihilate.lean) implements
this finite elimination; its verification status is recorded separately
in the associated build and exact-statement receipts.

## Direct replacement: barycentric ridge cut

In the simplex reconstruction proof, let \(\beta_j,\beta_k\) be
barycentric coordinates for two facets with the same nonzero sweep sign.
Put \(b_i=\beta_i'(e_1)\). Their \(b_j,b_k\) have the same nonzero sign.
The hyperplane
\[
 b_k\beta_j-b_j\beta_k=0
\]
contains their common ridge and is parallel to \(e_1\). On the opposite
edge its intersection satisfies
\(\beta_j=b_j/(b_j+b_k)\in(0,1)\). It therefore cuts the simplex into
two simplices, each retaining one chosen facet and replacing the other
by a facet parallel to \(e_1\). Other facets keep their normal directions
and signs. This is the same ridge cut as the two-dimensional projection
argument, with less construction and notation. The reconstruction error
identity and dimension estimates remain unchanged.

## Direct replacement: collect a generic finite simplex list

After the explicit caterpillar subdivision, write the result as
\(f=\sum_j a_jh_{P_j}+\rho\), with \(\rho\in L_{N-2}\).
The subsequent normalized-normal grouping only uses this finite list,
its original coefficients, and the common reconstruction operator.
Repeating the permutation, cut-set, and triangulation indices adds no
mathematical information. Repetitions in the list are allowed and retain
their weights, so this change loses no multiplicity information.

## Direct replacement: explain Boolean cancellation by a toggle

For
\(T_A=\sigma(\sum_{a\in A}d_a+\sum_{a\notin A}\sigma(d_a))\),
the identity \(\sum_A(-1)^{|A|}T_A=0\) has a two-case proof.
If some \(d_a\ge0\), toggling \(a\in A\) leaves \(T_A\) unchanged and
reverses its coefficient. If all \(d_a<0\), every \(T_A\) is zero.
The toggle also works at \(d_a=0\). This supplies a complete proof in a
sentence without changing the existing dimension bound for \(|A|\ge2\).

## Keep the remaining mechanisms

The rank-one reflection argument is already short: equivariance plus
the radial germ identity gives a linear opposite-face difference. A
geometric restatement in terms of translated exposed faces hides the
same calculation and is not a direct simplification.

The two-value cancellation still needs its neighboring-cut involution.
Reducing its two cases by spine reversal introduces another description
transport and does not currently shorten the audited proof.

Coordinate deletion must retain both endpoint fibres and the empty-cut
rooted-star correction. Discarding that correction or counting only
pendant insertions would change the coefficient identity. The existing
three-row insertion table is a compact way to preserve these obligations.

No simpler replacement for the common sweep reconstruction itself was
established here. The barycentric cut simplifies its implementation;
the reconstruction operator and the grouping of parallel facets remain
essential in this route.
