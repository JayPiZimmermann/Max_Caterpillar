# A nine-square coherent ordered facet lift

The first failed ordered lift has a short constructive repair. The
repair uses four squares whose coned classes vanish, rather than
averaging all label permutations. This is a chain identity for the first
lift, not a width-optimal five-input network or a uniform construction.

In the cubical chain product algebra, put

\[
 A=\partial\Delta_{012},\qquad
 B=\partial(-\Delta_{234}),\qquad Y=A\,B.
\]

Each triangle boundary is a three-segment cycle. Their product consists
of nine oriented parallelograms and is a cycle by the Leibniz rule:

\[
 dY=(dA)B-A(dB)=0.
\]

The factors lie in affine translates of the root lattice; adding their
basepoints puts every product square in the root lattice itself.

Five squares pair disjoint triangle edges. They have bases
`Delta_P-Delta_Q`, with

\[
(P,Q)=(12,34),(02,34),(01,34),(01,24),(01,23).
\]

These are exactly the preferred ordered tetrahedral representatives on
the five facets of the four-simplex, with their alternating facet
orientation signs. Coning each gives the corresponding tetrahedron
class, by the four-input identity in `overnight_upper_relative_nc.md`.

The other four squares pair edges meeting at the shared label 2. In
canonical positive edge directions `a,b`, each has head

\[
h=-a-b.
\]

Its base is `[-a,0]+[-b,0]`, which already contains the origin. Coning
does nothing: the result is a zonotope and is zero in the relevant top
class. Equivalently, its outer ReLU is redundant because

\[
\sigma(-a-b+\sigma(a)+\sigma(b))
=\sigma(-a)+\sigma(-b).
\]

Thus

\[
\rho(Y)=d[\Delta^4]
\]

with no facet symmetrization. All nine squares use noncrossing base
directions. The standalone integer checker independently verifies all
segment cancellations, the five induced facet signs, and the four
origin-corner identities.

This resolves the obstruction in `overnight_upper_ordered_lift.md`:
reweighting only the 30 nondegenerate base copies forces uniform
symmetrization, but allowing four elementary coning-kernel squares
repairs the preferred five-copy lift. A prior linear solve found a less
compact repair with two head-exchange relations and eleven squares;
the product cycle supersedes that representation for this purpose.

Two limitations remain. The augmentation of `Y` is nonzero, so it still
needs the augmentation correction and filling step before producing a
four-dimensional class. Also, products of more triangle boundaries do
not have the dimension required for higher simplex boundaries; there is
no immediate iteration of this formula. A uniform route needs an
ordered recurrence for these origin-corner corrections, with controlled
support and scaled-edge compression.

Producer and compact receipt:
`overnight_upper_ordered_product.py/.json`. The checker uses only the
Python standard library. This is not a Lean result.
