# A precise obstruction to a two-page higher-primitive recurrence

The normalized gap-graph complex has a uniform sparse contraction, but it
cannot be replaced by a contraction preserving noncrossing support. A natural
consecutive-interval higher-primitive recurrence also cannot stay on two
pages: its fifth equation fails for **every** choice satisfying the earlier
equations. This is an exact finite obstruction to the stated algebraic
recurrence. It does not exclude the noncrossing or two-page geometric
dictionary, for which no equivalence to this recurrence has been proved.

## The first necessary crossing state

Write $E_{ij}$ for a gap edge, with wedge order increasing lexicographically.
Set

\[
 A_{ijk}=E_{ij}E_{ik}+2E_{ij}E_{jk}+E_{ik}E_{jk}.
\]

For three consecutive gap positions the splitting differential gives
$\delta A=2E_{01}E_{23}$. Consequently

\[
 z=A_{012}E_{34}-E_{01}A_{234}
\]

is a six-term cocycle in exterior degree three and gap degree five. Every
term is noncrossing. It has no noncrossing primitive: the differential of
all 12 noncrossing three-edge source graphs has rank 12, whereas adjoining
$z$ gives rank 13. An exact dual functional is

\[
\begin{array}{c|r}
\text{graph}&\lambda\\ \hline
01,\ 12,\ 34&1/2\\
01,\ 13,\ 24&-1/2\\
01,\ 14,\ 23&1/2\\
02,\ 03,\ 14&-1\\
02,\ 13,\ 14&1
\end{array}
\]

and zero on the other gap graphs. It annihilates every allowed source
boundary and pairs to one with $z$. The source with all 16 gap graphs has a
primitive; one has 13 terms. Thus a crossing correction is needed already
for the difference between contracting the left two and the right two
consecutive edges.

The support test exhausts all noncrossing cocycles in exterior degrees two
through four, using all target rows. The first obstruction above is minimal
within that declared ordering. Noncrossing graphs are not a subcomplex:
splitting a shared endpoint can create crossing edges.

## The complete two-page test

Concatenating two gap graphs on disjoint consecutive blocks defines a
product $*$. If the left graph uses $q$ vertices, then

\[
 \delta(A*B)=\delta A*B+(-1)^q A*\delta B.
\]

Consider the specific higher-primitive equations

\[
 H_1=E_{01},\qquad
 \delta H_n=\sum_{i+j=n}(-1)^i H_i*H_j,\quad n\ge2,
 \tag{1}
\]

where $H_n$ has $n$ edges on $n+1$ gap positions. The right-hand side is
always a cocycle once earlier equations hold. Indeed, for a triple
$a+b+c=n$, the two occurrences of $H_a*H_b*H_c$ have signs
$(-1)^b$ and $-(-1)^b$.

A two-page graph means that its edges can be divided into two noncrossing
sets in the fixed gap order; equivalently its crossing graph is bipartite.
Its inventory is exponential in the number of gap positions. The question
was whether (1) could supply a coherent family inside this inventory.

The complete source dimensions and ranks are:

| $n$ | all source graphs | two-page source graphs | differential rank |
|---:|---:|---:|---:|
| 2 | 3 | 3 | 3 |
| 3 | 16 | 16 | 15 |
| 4 | 135 | 135 | 120 |
| 5 | 1581 | 1509 | 1357 |

The first primitive is unique, $H_2=-A_{012}/2$. All solutions for $H_3$
form a one-dimensional affine space. Each such choice lifts to $H_4$; its
remaining freedom has dimension 15. Hence the entire prefix through $H_4$
has 16 affine parameters. The fifth target remains affine in those
parameters, since it only contains $H_1*H_4$, $H_2*H_3$ and their reversals.
No parameters or orientation choices are omitted.

Adjoining all 16 gauge directions to the differential image does not raise
its rank: it is still 1357. Adjoining the fifth target raises the rank to
1358. An exact rational functional supported on just 31 of the 4410 target
graphs annihilates all 1509 allowed source boundaries and all 16 gauge
directions, and pairs to one with the target. The coefficients and complete
lower affine data are stored in
`overnight_upper_ordered_ainfty_affine.json`.

## Trust boundary and replay

The producer uses the edge-splitting differential and a bipartite-graph
search. The compact checker independently uses labelled half-edge
partitions and exhausts all two-colour assignments. It also verifies that
the stored lower kernels are complete, verifies the forced lifts of the
earlier gauge, and tests the 31-term dual functional directly. It does not
replay the large fifth RREF. The complete replay takes less than one second:

```sh
research/sN/dfs/h5-growth/venv/bin/python \
  research/sN/trees/overnight_upper_ordered_ainfty_check.py
```

The check receipt binds the certificate and checker hashes. All assertions
are exact rational identities. This is not a Lean proof.

The rejected claim is precisely that equations (1), with these consecutive
blocks and fixed gap order, admit two-page primitives through degree five.
The result does not show that every bounded-page recurrence fails, nor that
the original cubical lift requires this particular product equation.
Reopening conditions include a different marked boundary state, a
geometric recurrence avoiding (1), or a controlled family of crossing
motifs beyond two pages with a proved exponential total expansion.
