# Coherent ordered facet lifts without factorial averaging

This is a mathematical simplification of the homological route. It gives
an ordered recurrence and removes the sum over all injective label maps.
It does not yet give an exponential support bound for repeated fillings.
No Lean verification is claimed.

Use the cubical complex `C` and the polytope complex `P` of BHR+, with
their coning convention: the orientation of the cone over `(h;e_1,...,e_k)`
is `e_1 wedge ... wedge e_k wedge h`. Coning commutes with boundaries
for cubical degree at least two. Write `X_n in C_(n-1)` for a lift of
the oriented `n`-simplex on labels `0,...,n`.

For an increasing injection `mu`, use the **linear root-lattice map**

\[
 \psi_\mu(e_j-e_i)=e_{\mu(j)}-e_{\mu(i)}.
\]

These maps send zero to zero. They are not affine maps carrying the
original simplex vertices to the vertices of a larger simplex. A facet
is translated so its own first vertex is zero; that translation is
irrelevant in `P`, but it must not be erased in the cubical complex.
The linear maps compose functorially, commute with cubical boundaries
and coning, and commute with doubling/subdivision.

Let `delta` be the alternating sum of the `n+1` increasing facet maps.
The standard face identities give `delta^2=0`. In `P`, if
`rho(X_(n-1))=[Delta_(n-1)]`, then

\[
 \rho(\delta X_{n-1})=d[\Delta_n].                    \tag{1}
\]

## The low-degree base is coherent

Let `Gamma_ijk` be the positively oriented triangular edge cycle on
the points `0,e_j-e_i,e_k-e_i`. Set

\[
 X_2=-\Gamma_{012}.
\]

It is a cubical cycle. Its two edges through zero have degenerate cones;
the opposite edge has cone orientation opposite to the triangle.
Therefore `rho(X_2)=[Delta_2]` with the displayed minus sign.

The chain `Y_3=delta X_2` is nonzero. In fact, writing `E_ij` for the
unit cubical edge in direction `e_j-e_i` and `g_ij` for translation by
that vector, one has

\[
 Y_3=(g_{01}-1)\Gamma_{123},\qquad
 X_3=E_{01}\,\Gamma_{123},\qquad dX_3=Y_3.            \tag{2}
\]

Here the product is the cubical exterior product, including its
orientation signs. The first equality is a literal six-segment chain
identity. Its augmentation vanishes, but the chain itself does not.
Coning `Y_3` gives the four translated triangular facets of the
tetrahedron with their correct signs. Coning `X_3`, using the chain-map
identity in degree two and injectivity of the top boundary, therefore
gives `[Delta_3]`.

This checks precisely the issue that affine facet embeddings would
hide: affine copies of triangle boundaries cancel by boundary-squared,
while the required linear root-lattice copies are based at different
local origins. Only their augmentations cancel.

The next ordered boundary has a compact identity as well:

\[
 \delta X_3
 =-\Gamma_{012;\,2,-}\,\Gamma_{234;\,2,+}.            \tag{3}
\]

The subscripts after the semicolon specify the attachment vertex and
reflection. Thus this is a nine-square product of two closed triangle
cycles. It recovers the earlier five-label product lift from the ordered
recurrence rather than guessing it independently.

`overnight_upper_ordered_coherent.py` checks (2), (3), all cubical
boundaries, the zero augmentation, `delta^2 X_2=0`, the triangle coning
sign, and the full nonzero tetrahedral target image. The latter check
uses oriented vertex triangles modulo translation, not Fourier samples.

## The ordered induction

For a degree-`k` chain let `S_k` be doubling followed by cubical
subdivision. For a cycle and `k >= 2`, define

\[
 D_k=\frac{2^k\operatorname{id}-S_k}{2^k-2}.
\]

Then `D_k` preserves cycles and their coned images and kills augmentation.
It commutes with every facet embedding. Starting with the explicit `X_3`
in (2), define, for `n >= 4`,

\[
 Y_n=\delta X_{n-1},\qquad
 dX_n=D_{n-2}Y_n.                                    \tag{4}
\]

The right side is fillable. First, `Y_4` is a cycle because
`dY_4=delta dX_3=delta^2 X_2=0`. For `n >= 5`, the previous exact
boundary identity gives

\[
 dY_n=\delta D_{n-3}\delta X_{n-2}
     =D_{n-3}\delta^2X_{n-2}=0.
\]

Now `D_(n-2)Y_n` has augmentation zero, so the cubical filling theorem
provides `X_n`. Equation (1), preservation of the coned image by `D`,
and the coning chain-map identity imply

\[
 d\rho(X_n)=\rho(dX_n)=\rho(Y_n)=d[\Delta_n].
\]

Injectivity of the top differential yields `rho(X_n)=[Delta_n]`.
This proves the recurrence for every arity. It uses one ordered copy
per facet; arbitrary choices of filling do not spoil the next step,
because their exact cubical boundary is fixed by (4).

The face-direction condition is also preserved: every cube in `Y_n`
lies in a facet edge span, and doubling/subdivision keeps it there.
Thus `dX_n` has the condition required by the original homological route.

## The quantitative residual

The recurrence removes factorial symmetrization at each stage. It does
not prove that repeated fillings have exponentially many distinct cubes.
Using the earlier generic filling bound independently in every dimension
still accumulates an exponent quadratic in `n`; long edges also require
care when reused as inputs. A compact expression graph indexed by
ordered label subsets alone is not a width bound, since applying a
filling changes the individual dictionary functions.

The concrete next target is a filling operator compatible with the
ordered recurrence whose total expansion is `C^n poly(n)`. The explicit
segment-times-cycle base in (2), and the product factorization in (3),
provide exact nonproduct states for testing such an operator. No claim
of an exponential construction follows merely from removing the
factorial averaging.
