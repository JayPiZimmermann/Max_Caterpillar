# Symmetric clique bases cannot give the uniform construction

The following is a mathematical exclusion of one continuous family. It
does not exclude arbitrary clique heads, independently weighted clique
edges, general multipartite graphs, or the requested general exponential
construction. It is not Lean verified.

For a nonempty subset `S` and an apex `a` outside it, consider

\[
 U_{a,S;c,\lambda}(x)=
 \sigma\left(c(\operatorname{mean}_S x-x_a)
       +\lambda\sum_{\{i,j\}\subset S}|x_i-x_j|\right),
 \qquad c,\lambda\in\mathbb R.
\]

**For every `N>=5`, `max_N` is outside the linear span of all these atoms,
even with an arbitrary `L_(N-2)` remainder.** All label subsets, all real
parameters, and arbitrary real output coefficients are allowed in this
statement.

Write `V_S=sum_{i<j in S}|x_i-x_j|`. The cases `c=0` are shallow.
Positive scaling reduces the other heads to `delta(mean_S-x_a)` with
`delta` equal to `+1` or `-1`. Negative inner weights can be removed modulo
shallow functions, since for `t>=0`

\[
 \sigma(\delta h-tV_S)
 =\sigma(-\delta h+tV_S)+\delta h-tV_S.
\]

It therefore suffices to take `lambda>=0` and `delta=+-1`.

Let `T_j` mean the signed directional derivative in direction `-e_j`,
followed by setting the deleted coordinate to zero. It lowers the
filtration by one and satisfies

\[
T_j\max_I=\max_{I\setminus\{j\}}
\]

up to a linear term, whenever `j` is a remaining input label.

Consider a full atom with `s=|S|`. Deleting its apex gives a shallow
function. For a nonapex label `j in S`, the two inner slopes in directions
`-e_j` and `+e_j` are respectively

\[
-\delta/s+\lambda(s-1),\qquad
 \delta/s+\lambda(s-1).
\]

A nonzero slope makes the outer derivative either zero or the shallow
inner derivative. A zero slope is possible only at

\[
 \lambda=\frac1{s(s-1)}.
\]

At that value the surviving outer atom has the **same** `delta` and
`lambda`, with `S` replaced by `S\setminus\{j\}`. Indeed its coefficient
on each remaining coordinate is

\[
\frac\delta s+\delta\lambda=\frac\delta{s-1}.
\]

More precisely, modulo `L1`,

\[
T_j U_{a,S;\delta,\lambda}
 =\begin{cases}
 \delta U_{a,S\setminus\{j\};\delta,\lambda},
     &\lambda=1/[s(s-1)],\\
 0,&\text{otherwise}.
 \end{cases}
\]

The next smaller atom would need the different value
`1/[(s-1)(s-2)]` to survive another nonapex deletion as an outer atom.
Consequently **any three distinct coordinate deletions send every full
atom into `L0`**: there is at most one surviving outer-atom step, followed
by a shallow step and a linear step. Any previously accumulated shallow
terms also become linear or zero. This includes sequences that delete the
apex at any stage.

Now apply three fixed distinct deletions to a proposed representation of
`max_N`. A proper-subset atom is a function of at most `N-1` coordinates,
is invariant under their common translation, and is a difference of
support functions in dimension at most `N-2`; it already belongs to
`L_(N-2)`. The assumed remainder and all proper-subset atoms therefore
land in `L_(N-5)`. Full atoms land in `L0`, which is contained in
`L_(N-5)` for `N>=5`. But the target becomes `max_(N-3)`, whose simplex
has dimension `N-4` and whose class is nonzero modulo `L_(N-5)`.
This is a contradiction.

The proof concerns the displayed atoms themselves. It does not assert
that every face of a permutohedral pyramid has the same symmetric head
and uniform clique weight. Adding unrestricted face functions is a
different family and requires a separate argument and size count.

The exact finite chamber calculations in
`overnight_upper_permutohedron.py` motivated this argument. For the listed
nonnegative rational values `lambda=p/q`, `0<=p<=6`, `1<=q<=6`, both head
signs and all subsets, the ranks are recorded in the accompanying JSON
receipts. The uniform proof supersedes the finite exclusion at five
inputs and above; the four-input finite failure remains narrower than an
all-real statement.
