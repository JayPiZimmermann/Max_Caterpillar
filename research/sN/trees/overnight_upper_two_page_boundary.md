# Two noncrossing pages repair the first ordered boundary obstruction

The current positive result is an exact **six-label coherent boundary
lift** using one fixed cyclic label order and two noncrossing pages.
It is not an all-arity construction or an emitted maximum network.

For a triangle `T={i,j,k}`, an attachment vertex `r in T`, and a sign
`epsilon=±1`, write

\[
\Gamma_{T,r}^{\epsilon}
 =\partial\operatorname{conv}\{0,
       \epsilon(e_i-e_r),\epsilon(e_j-e_r),\epsilon(e_k-e_r)\}.
\]

The repeated zero at the attachment is ignored. This is a three-segment
cycle. Products of `N-3` such cycles are cubical cycles of degree `N-3`,
the degree needed to lift the boundary of the `(N-1)`-simplex.
Changing an attachment translates a factor. That translation changes
the result after coning, even though the factor remains a cycle.

## The exponential candidate and the exact finite distinction

Choose two triangulations of the same cyclically ordered `N` labels,
then choose `N-3` distinct triangular faces from their union. Each chosen
face has three attachment choices and two reflection choices. There are
fewer than

\[
16^N\,4^N\,6^N=384^N
\]

descriptions: two Catalan triangulations, a subset of at most `2N-4`
faces, and six local choices. Expanding each product gives at most
`3^(N-3)` cubes. Thus even its complete cubical description family is
exponential. This count alone does not prove that it contains a simplex
boundary lift.

The smallest controls distinguish three scopes:

| Six-label boundary family | Exact ordinary / augmented rank |
|---|---:|
| Common attachment vertex, all three forest shapes, all reflections, all label orders | 3 / 4 |
| One fixed cyclic order, one triangulation, one omitted face, all local attachments/reflections | 173 / 174 |
| A two-page subfamily from six product types, fixed cyclic order, dihedral averaging | 129 / 129 |

The middle exclusion uses all 279 exact rational right-kernel relations,
together with an augmented modular minor. The positive last row was
verified by exact principal-part identities on every supporting-hyperplane
orbit. It uses **eight** dihedral product orbits, each containing at most
12 products, with coefficients `-1/15` and signs of `1/20`.

The compact certificate `overnight_upper_two_page_witness_6.json` stores
the eight products, their coefficients, and explicit page colorings.
The checker `overnight_upper_two_page_witness.py` needs no search matrix.
It verifies the formal cubical cycle equations and the coned boundary
identity. After combining terms there are 1,006 formal cubes and 18
supporting hyperplanes in four dihedral orbits. A fresh replay takes
under a second in the recorded environment.

The augmentation has 312 nonzero coefficients. Thus the witness still
needs the augmentation correction and a filling before it yields a
top-dimensional maximum identity. It is not a 96-unit network claim.
The count of product cycles and the count of network functions are
different quantities.

## Why direct product induction loses information

There is a precise five-label crossing relation, with all factors
attached at label zero:

\[
\rho(\Gamma_{012}^{+}\Gamma_{034}^{-}
       +\Gamma_{013}^{+}\Gamma_{024}^{-})=0.
\]

Multiplying this cycle by `Gamma_045^+` destroys the relation. On the
six-label hyperplane with normal `(0,0,0,0,0,1)`, the rational function
of the coned product at coordinates `(1,16,15,11)` is exactly

\[
\frac{7}{1684800}\ne0.
\]

The producer `overnight_upper_product_congruence.py` checks the original
relation exactly on all its hyperplanes and records the nonzero rational
witness after multiplication. Consequently the coning kernel is not a
product ideal. A valid recurrence must retain a correction state rather
than replace a lower cycle only by its coned class.

The simplest exterior-ear continuation also fails exactly at seven
labels. Insert a new label between the old cyclic neighbors, append
the triangle on these three labels, and allow every attachment and
reflection of that triangle. Applying this to every dihedral image of
the eight positive six-label product types gives 270 product columns
with ranks 263 / 264. All seven right-kernel relations passed exactly.
This excludes that restricted ear recurrence, not the complete two-page
family.

## What a uniform lift would still need

A uniform boundary identity in the displayed exponential family would
avoid dimension-by-dimension facet symmetrization. For a degree-`k`
unit-root cube cycle `Y`, the established doubling correction

\[
Y'=(2^kY-SY)/(2^k-2),\qquad k\ge2,
\]

has zero augmentation and the same coned class. It uses at most
`(1+2^k)` times as many unit-root cubes. The one-step filling observation
in `overnight_upper_koszul_filling.md` would then apply once, with its
`n*9^k` bound and one possible long star edge per output description.
There is no repeated scaled-input issue in that one-step application.

The unsolved step is the coherent all-arity boundary identity. The
seven-label ear failure shows that a single old coned identity does not
supply enough attachment data. A controlled translation repair also
fails: translate the whole old cycle by zero or by either sign of
`e_new-e_left` or `e_new-e_right`, then adjoin any of the six rooted and
reflected ears. These 30 states have exact ranks 8 / 9, with all 22
right-kernel relations checked. This does not exclude translating
constituent products independently or attaching the new triangle at
non-neighboring old labels. More general relative-chain states remain
open.

All conclusions here are research mathematics and exact finite
certificates. None has been formalized in Lean, and none establishes a
uniform exponential maximum construction.
