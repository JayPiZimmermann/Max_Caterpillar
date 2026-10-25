# A quantitative one-step Koszul filling observation

This is a proposed refinement of the homological route in BHR+, not an
exponential construction. The input-direction restriction below is
essential. The argument is mathematical and has not been formalized.

Choose star directions `t_1,...,t_n` as a lattice basis. Write `g_i` for
translation by `t_i`, `e_i` for the corresponding Koszul generator, and
`d(e_i)=g_i-1`. Every other **unit root direction** is
`b=t_j-t_i` (with the obvious convention for a root endpoint), and
`g_b=g_j g_i^(-1)`. Define

\[
z_b=e_b-g_i^{-1}e_j+g_i^{-1}e_i.
\]

Then `d(z_b)=0`, and this triangular change of exterior generators gives
an explicit chain isomorphism

\[
C_\bullet\cong K_\bullet(g_1-1,\ldots,g_n-1)
                 \otimes\bigwedge\langle z_b\rangle.
\]

Consider a degree-`k` cycle `x` with augmentation zero, written as `M`
translated unit root-direction cubes. Each input wedge expands into at
most `3^k` terms in the new generators. The augmentation-zero condition
remains true after the generator change, since its augmentation is an
invertible linear change of exterior basis.

Use the standard tensor-product contraction of the star-basis Koszul
complex onto its augmentation. On a monomial translated cube, at most
`n` coordinate contractions are nonzero. Each is a consecutive string
of unit cubes along one star direction, with all other directions fixed.
After coning, the string can be represented by one pyramid over a
zonotope with one long star edge: subdivision changes only lower
dimensional face terms. Negative translation exponents merely reverse
the interval orientation and output sign.

Expanding each remaining `z_b` back into root and star generators costs
at most another `3^k`. Thus, **for this one filling step**, the resulting
coned class has a description by at most

\[
 M n 9^k
\]

pyramids over zonotopes. The heads may be arbitrary lattice translations;
the output generators are unit root directions except for the one long
star edge introduced by the contraction. Scaled coordinate differences
do not need new first-hidden-layer directions: their magnitudes can be
absorbed into the inner coefficients.

This removes the apparent `n^k` cost of eliminating nonbasis directions
one at a time. It does not solve the full induction. In particular:

* A long output edge can become a nonbasis direction after the next
  facet embedding. In the original unit-generator complex,
  `e_(m b)=(1+g_b+...+g_b^(m-1))e_b`. Changing basis can expand that
  series into `m` translates. The above count does not control arbitrary
  scaled input edges.
* Applying an exponential-cost filling separately in every dimension
  still gives a bound exponential in `n^2`, before addressing the
  factorial facet symmetrization.
* A coherent ordered facet lift, and compression compatible with
  subdivision and the generator change, remain necessary for an
  exponential bound in `n`.

The source comparison is the homological construction in
`research/sN/best5/lit/2610.28587v1.txt`, especially its Koszul filling
proof and Lemmas 11--12. The observation above concerns the concrete
filling operator only; it does not alter the cited paper's theorem or
claim a width bound supplied by that paper.
