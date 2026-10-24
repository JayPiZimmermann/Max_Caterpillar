# All balanced interval hierarchies: count review

24 October 2026. The fixed padded hierarchy is excluded at seven inputs.
The following family is a genuine enlargement. Its exponential size is proved
here; its sufficiency is open.

On an ordered interval with `n` labels, allow every split after position `k`
with `n/3≤k≤2n/3`. Recursively choose a hierarchy on each resulting interval,
and choose one arbitrary bridge between the two vertex sets. Let `B_n` count
these descriptions, allowing different descriptions of the same labelled
tree. Then

\[
B_1=1,\qquad
B_n=\sum_{\lceil n/3\rceil\le k\le\lfloor2n/3\rfloor}
k(n-k)B_kB_{n-k}.
\]

Every described graph is a tree: the two child trees are disjoint and a single
bridge joins them. Duplicate descriptions only reduce the number of distinct
trees. An elementary induction gives

\[
\boxed{B_n\le\frac{14^{n-1}}{n^3}.}
\]

The cases `n=1,2` are immediate (`B_2=1≤14/8`). For `n≥3`, assume the bound
at smaller sizes. There are at most `n/3+1≤2n/3` allowed integer split
positions, and every allowed split satisfies `k(n−k)≥2n²/9`. Hence

\[
\begin{aligned}
B_n
&\le14^{n-2}\sum_k\frac1{k^2(n-k)^2}\\
&\le14^{n-2}\frac{2n}{3}\frac{81}{4n^4}
=14^{n-2}\frac{27}{2n^3}
\le\frac{14^{n-1}}{n^3}.
\end{aligned}
\]

Thus all five edge states, every apex and head root, cyclic starting points,
and reversal give at most `poly(N)70^N` descriptions. The proposed looser
`poly(N)105^N` bound was also valid. Union with the old pruned family retains
the `poly(N)70^N` bound, since the latter has at most `4^(n−1)` trees before
the polynomial choices. This union matters at sizes where the old root split
is unbalanced; inclusion should not be assumed without it.

At six nonapex labels the new `3+3` split already supplies trees outside the
old family. One example has edges

\[
01,\ 12,\ 14,\ 34,\ 45.
\]

Its two interval triples are trees and `14` is their bridge. It contains
neither adjacent perfect matching `01,23,45` nor `12,34,50`, whereas every
tree in the old six-label cyclic hierarchy contains one of those matchings.
It therefore survives the precise scope audit of the old-family obstruction.

No top-class identity for this enlarged family follows from the recurrence.
The full edge-gluing factorization in `gluing_review.md` applies, but a closed
linear identity with the external frequency parameter is still needed.
