# A polynomial-sparse contraction of the normalized exterior graph complex

This is an explicit uniform algebraic contraction, with exact finite convention
checks. It is not an exponential-width construction of the maximum function.
The outstanding issue is controlling the total geometric support across all
stages of the coherent lift, including coordinate conversion and filling.

## Partition model and the one-letter contraction

Fix $2k$ distinct half-edge letters. In degree $q$, use ordered partitions

\[
 P=(B_1|\cdots|B_q)
\]

of those letters into nonempty blocks. The differential splits block $B_i$
into every ordered pair of nonempty complementary subsets, with sign
$(-1)^i$. In particular it raises $q$, and its square is zero: disjoint
splits cancel in opposite orders, as do the two ways of obtaining three
successive pieces of one block.

For a distinguished letter $a$, define $P_aP=0$ unless $a$ forms a
singleton block $B_i=\{a\}$. In that case move that block to the right end
and multiply by $(-1)^{q-i}$. Define

\[
 H_aP=(-1)^i\sum_{j>i}
 (B_1|\cdots|\widehat{\{a\}}|\cdots|B_j\cup\{a\}|\cdots|B_q)
\]

in the singleton case, and zero otherwise. Then

\[
 \delta H_a+H_a\delta=1-P_a. \tag{1}
\]

This is a direct cancellation identity. Splits outside the receiving block
cancel between the two compositions. Splits of the receiving block with
$a$ still attached cancel with the corresponding summand of $H_a\delta$.
The remaining terms separate $a$ from its receiving block and telescope as
that block moves to the right, leaving the original partition and its signed
terminal singleton projection. If $a$ was not a singleton, only the two
splittings that isolate $a$ enter $H_a\delta$; their receiving-block
sums telescope to the original partition. This also proves that $P_a$ is
a cochain map. Each $H_aP$ has at most $q-1$ terms.

## An even permutation and the exterior quotient

For distinct letters $a,b$, put $Q=P_bP_a$. Swapping $a,b$ gives
$Q(a\ b)=-Q$: if either letter is not singleton both sides vanish; if both
are singletons, their two terminal positions are transposed. Thus

\[
 H_{a,b}=(H_a+H_bP_a)(1+(a\ b)),\qquad
 \delta H_{a,b}+H_{a,b}\delta=1+(a\ b). \tag{2}
\]

Given two edge pairs $(a,b),(c,d)$, let

\[
 J=H_{a,c}-(a\ c)H_{b,d}.
\]

The transpositions are disjoint, so

\[
 \delta J+J\delta=1-(a\ c)(b\ d). \tag{3}
\]

The graph quotient is the character quotient for
$G=(S_2)^k\rtimes S_k$: reversing one edge and exchanging two edge factors
both have character $-1$. Projecting a partition places its two half-edge
letters at their block positions, orders each edge increasingly, and sorts
the list of edges with exterior signs. Loops and repeated edges vanish.
Every resulting graph has no isolated vertex. This is exactly the
normalized complex $\Lambda^k(\Lambda^2V)$ in adjacent-gap coordinates.

Average $J$ over the $4k(k-1)$ choices of an ordered pair of distinct
edge factors and one selected endpoint of each. This is its full conjugacy
average under $G$, without enumerating the unused permutations: the
formula depends only on the four marked half-edges and is natural in all
unmarked letters. It therefore descends to the graph quotient. Each
$(a\ c)(b\ d)$ exchanges two edge factors, so acts as $-1$ on that
quotient. Dividing the average by two gives

\[
 \boxed{\delta h+h\delta=1\quad(k\ge2).} \tag{4}
\]

This proves acyclicity and provides a primitive for every cocycle without
solving a linear system or invoking an existence-only comparison theorem.

## Quantitative scope

Before cancellations, $H_{a,b}$ has at most $4(q-1)$ terms and $J$
at most $8(q-1)$. Thus $h$ produces at most

\[
 32k(k-1)(q-1)
\]

graph terms per input graph; its only new common denominator is
$8k(k-1)$. A gap-graph wedge of degree $k$ lifts to at most $12^k$
original root-edge cubes: each gap edge expands into at most four root
triangle cycles, each triangle cycle into three segments.

These bounds apply to one primitive operation. Applying them successively
at every arity can still have superexponential total support. Converting an
arbitrary root-coordinate wedge into gaps can itself have many terms.
Neither difficulty is removed by (4). A compact circuit of these operations
is not by itself a two-hidden-layer network of comparable width.

## Reproducible controls

`overnight_upper_ordered_sparse_homotopy.py` checks (1)–(3) on all 633
ordered partitions of at most five letters; it checks (4) on every graph in
exterior degrees two and three, and 115 declared graph controls in degree
four. It reproduces the independently computed two-edge inverse exactly.
The largest primitive supports in those checks are 3, 25, and 113 terms.

`overnight_upper_ordered_sparse_support.py` separately tests fixed-order
noncrossing support. The present homotopy already leaves it at $k=3,q=5$:
the noncrossing input \(\{01,02,34\}\) has an output
\(\{02,03,13\}\) with coefficient $-1/12$. This specific failure does not
exclude another homotopy or the noncrossing geometric dictionary.

Run with `research/sN/dfs/h5-growth/venv/bin/python`; the JSON receipts record
the producer hashes and the finite domains. None of these results is Lean
verified.
