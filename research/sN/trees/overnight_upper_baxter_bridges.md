# Sparse cyclic graphs: positive bridges and the missing recurrence

25 October 2026. The live candidate consists of an apex star together with
the union of a twin binary-search-tree pair in one fixed label order.
It has at most $3N-5$ edges. The twin pairs number at most $16^{N-1}$;
all five segment states and all roots therefore still give
$\operatorname{poly}(N)2000^N$ descriptions. This is an enumeration bound,
not a uniform construction theorem.

The geometric formula and its exact spanning-two-forest normal form are
in `overnight_upper_baxter_apex_geometry.md`. All experiments here use
that unchanged five-state family. No arbitrary relabeling closure or
expanding head alphabet is implicit in the count.

## Two positive bridges

The established exact five-input network with widths $(9,18)$ has a
comparison graph contained in the candidate graph

\[
 \{01,02,03,04,12,13,24,34\}.
\]

The following scalar identities hold for arbitrary real $A,y$:

\[
\begin{aligned}
\sigma(A-\sigma(y))
 &=\sigma(A)+\sigma(A-y)-\sigma(A+\sigma(-y)),\\
\sigma(A+2\sigma(y))
 &=\sigma(A+\sigma(y))+\sigma(A+y+\sigma(y))-\sigma(A+y).
\end{aligned}
\]

They follow separately on $y\ge0$ and $y\le0$ by cancellation of identical
outer arguments. The first identity applies to any negative magnitude
by rescaling $y$. These are whole-function identities, so their
lower-dimensional terms must be retained.

Applying them to the known network produces 1,297 positive unit-length
zonotope-pyramid terms. Visible-facet decomposition and graphic tiling,
now in the top quotient, combine them into **59** nonzero forest atoms.
Every one of the 59 belongs to the original five-state family, with its
original canonical root/apex head plus allowed frozen segments.
Their rational Fourier sum is exactly the simplex kernel.

The known seven-input noncrossing witness also embeds completely.
Of its 6,909 supported units, 6,878 embed as whole functions. If its old
apex is $a$, root is $r$, and the selected graph centre is $b\ne r$,
the head equality is

\[
 x_r-x_a=(x_r-x_b)+(x_b-x_a).
\]

The last term is one frozen star edge; it is absent from the free tree
because $a$ was isolated. The remaining 31 units have graph centre
$b=r$. Reverse every input coordinate: the new canonical head is
$x_a-x_r$ and all inner orientations reverse. Reflection multiplies
the generic Fourier kernel by $(-1)^7$, so these are top-class
embeddings. There are no uncovered units.

`overnight_upper_baxter_bridge_check.py` independently verifies both
positive identities. It obtains each forest kernel by inverting the
matrix whose rows are the head and free-edge forms. It does not use
the producer's rooted cut sums or zonotope tiling. It also reconstructs
the BSTs by insertion, independently of the recursive producer.
The compact seven-input receipt contains every atom, coefficient and
embedding word; replay does not require the large search inventory.

These are finite positive controls of a family with an exponential
description count. A uniform top-class recurrence is still missing.
The original scalar conversion is exact, but the 59-atom conversion
and reflected seven-input embeddings are top-class statements.
They do not by themselves give new exact networks without the
lower-dimensional correction argument. Adjoining all faces and all
label-subset instances preserves exponential size; sufficiency of
that closure still requires the uniform identity.

## A valid operator and a failed local realization

For a function on $N$ labels define

\[
 S_a f(x_0,\ldots,x_N)
 =f(x_0,\ldots,\max(x_a,x_N),\ldots,x_{N-1}).
\]

This operator is linear in $f$ and sends $\max_N$ exactly to
$\max_{N+1}$. It maps $L_k$ into $L_{k+1}$: a function depending on
$k$ linear features acquires at most the one additional linear feature
$x_N-x_a$, followed by a CPWL operation. A DC decomposition in this
feature space gives the claimed dimension bound.

Writing $\bar\omega_a=\omega_a+\omega_N$ and leaving the other old
frequencies unchanged, integration over the two halfspaces
$x_a\ge x_N$ and $x_N\ge x_a$ gives the generic Fourier rule

\[
 R_{S_af}(\omega)
 =-\left(\frac1{\omega_a}+\frac1{\omega_N}\right)
     R_f(\bar\omega).
\]

The sign is fixed by the simplex kernel
$(-1)^{N-1}/\prod_i\omega_i$.

The first local candidate splits the vertex $a$ of the full
head-plus-hinge tree, distributes its incident edges between $a$ and
the new label, and adds their connecting edge. It allows every head
placement and every orientation on every resulting tree.
For

\[
 U=\sigma(x_1-x_0+\sigma(x_1-x_2)+\sigma(x_2-x_3))
\]

the finite exact results are:

| Split label | Columns | Ordinary / augmented rank | Result |
|---|---:|---:|---|
| 0 | 60 | 44 / 44 | Exact three-term top identity |
| 1 | 112 | 80 / 81 | Excluded |
| 2 | 112 | 80 / 81 | Excluded |
| 3 | 60 | 44 / 45 | Excluded |

For the leaf split, allowing the third spanning tree of the triangle
on labels $2,3,4$ still gives ranks **58/59**. Thus this particular
triangle completion is also insufficient.

Every needed right-kernel relation was checked as an exact rational
identity. `overnight_upper_baxter_split_check.py` independently
recomputes the entire evaluation matrices by coordinate inversion,
checks the augmented ranks, proves all right-kernel identities and
checks their independence. These exclusions concern the stated local
canonical tree rules. They do not exclude broader cyclic formal states.

## Why an opaque scalar remainder cannot be the state

There is also a uniform obstruction to treating the unaffected remainder
as a free scalar $t$. Consider

\[
 F(t,p,q)=\sigma\bigl(t+\sigma(-\max(p,q))\bigr).
\]

Every finite sum of two-hidden-layer units whose first-hidden-layer
functions are independent of $t$, with arbitrary $t$-linear outer
heads and arbitrary shallow remainder, has $D_{e_t}$ in $L_1$.
For a unit with outer coefficient $c\ne0$, this derivative is
$\operatorname{sgn}(c)$ times its entire preactivation; for $c=0$
the two directional germs cancel.

But $D_{e_t}F=t+g(p,q)$, where
$g=\sigma(-\max(p,q))$ is not shallow. Its odd part fails additivity:
for $u=(-1,0)$ and $v=(0,-1)$,

\[
 [g(u+v)-g(-u-v)]-[g(u)-g(-u)]-[g(v)-g(-v)]=1.
\]

Every shallow homogeneous ReLU sum has linear odd part. This also
excludes equality modulo $L_2$ in the three-dimensional $(t,p,q)$
space, since $D_{e_t}$ sends that remainder into $L_1$.

A useful recurrence must therefore activate a head-dependent
first-hidden-layer feature, or keep a correlated collection of terms
whose nonshallow germs cancel. Applying the rule to an arbitrary
opaque graft remainder is impossible. The next target is such a
correlated cancellation state, not another finite head alphabet.

## Replay

Run with the existing `h5-growth` Python environment:

```
python research/sN/trees/overnight_upper_baxter_bridge_check.py
python research/sN/trees/overnight_upper_baxter_split_check.py
```

All claims here are mathematical proofs or finite symbolic certificates.
No new Lean verification or uniform exponential construction is claimed.
