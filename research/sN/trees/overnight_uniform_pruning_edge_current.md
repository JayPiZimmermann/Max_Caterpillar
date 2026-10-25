# Odd-tree currents: valid identities and a failed descent

The complete-graph-Laplacian score below **does not descend to functions**.
The independent checker gives an elementary five-label equality on which the
scores disagree. The combinatorial current identities remain valid and expose
two distinct consistency conditions a future matching invariant must satisfy.
The subsequent `overnight_uniform_pruning_current_no_go.md` proves the stronger
result: even an arbitrary zero-sum auxiliary vector in this current form
cannot give a matching separator at five labels.

Let (B) be a tree on (2q+1\ge3) ordered labels. Let (J_v) be the sign sum
of linear extensions of the edges directed away from root (v).

* (J_v\ne0) exactly when (B-v) has a perfect matching. Pair positions
  ((2,3),(4,5),\ldots) after the forced first vertex (v), and swap the first
  incomparable pair. Survivors are the domino extensions of the unique perfect
  matching of (B-v); all have the same sign.
* (\sum_vJ_v=0). Rooted extensions across all roots are exactly the orders
  whose nonempty prefixes induce connected subtrees. Swapping the first two
  labels preserves this property and reverses permutation sign.
* If deleting edge (H=uv) leaves matching number less than (q), then
  (J_u=J_v=0) and the sum of (J) on either component of (B-H) is zero.
  Indeed, write the two component orders as odd and even. Every exposable
  vertex in the odd component would give a size-(q) matching avoiding (H),
  so none exists. If an endpoint were exposable, its perfect matching would
  also avoid the missing endpoint's edge (H), again a contradiction. The
  other component sum is zero because the total sum is zero.

For any zero-sum vector (K), orient each edge (H=u\to v) and write

\[
 S_H(J)=\sum_{w\text{ in the }u\text{-side}}J_w,
 \qquad
 Q_H=S_H(J)(K_u-K_v)-S_H(K)(J_u-J_v).
\]

Discrete integration by parts gives
\(\sum_H S_H(J)(K_u-K_v)=\sum_vJ_vK_v\), hence
\(\sum_HQ_H=0\). If (K) transforms by the same permutation sign as (J),
then each (Q_H) is label invariant. It also vanishes on every edge whose
deletion has matching number below (q), by the preceding support facts.
These properties match the full head-exchange identity, but do not imply
compatibility with all equal presentations of a dictionary function.

Take (\kappa_v=\operatorname{outdeg}_B(v)) and
\(K=L_{\mathrm{complete}}(\kappa J)\), where
\(K_v=(2q+1)\kappa_vJ_v-\sum_w\kappa_wJ_w\).
On a canonical leaf head (H=(r,a)), (J_r=0), so

\[
 Q_H=-J_aK_r=J_a\sum_v\kappa_vJ_v.
\]

This proposed score fails on

\[
\begin{aligned}
 U_1&=\sigma(x_1-x_0+\sigma(x_2-x_1)+\sigma(x_3-x_1)+\sigma(x_2-x_4)),\\
 U_2&=\sigma(x_1-x_0+\sigma(x_2-x_1)+\sigma(x_1-x_3)+\sigma(x_4-x_2)).
\end{aligned}
\]

After exchanging labels (1\leftrightarrow2) and (3\leftrightarrow4), the
first unit equals the second by
\(x_2+\sigma(x_1-x_2)=x_1+\sigma(x_2-x_1)\).
Their full permutation sums therefore agree as whole functions, while their
current scores are respectively (-1) and (0).

This is a **head-transfer** obstruction. On any nonapex tree, replacing a
head (x_r-x_a) and segment function (\sigma(x_s-x_r)) by head

\[
 x_s-x_a\quad\text{and}\quad\sigma(x_r-x_s)
\]

does not change the unit. The invariant coefficient vector on the nonapex
tree is (\kappa=\operatorname{outdeg}_T+e_r); it is unchanged by this move.
The augmented tree, and hence the odd rooted vector (J), does change.
Any corrected current must respect both this transfer and the augmented-tree
head-exchange identity. No uniform matching separator is proved here.

## The direct root-slide repair also fails

One can sum or average the score over every representation obtained by moving
the positive head along incoming segment edges and the negative head along
outgoing segment edges. This is invariant under head slides by construction.
It does not retain head-exchange compatibility.

Take the oriented five-label path with edges, in order,

```
(1,0), (1,2), (0,3), (3,4).
```

Use each edge in turn as the head, keeping the other three as segment
functions. The four slide orbits contain respectively `3,1,4,3` presentations.
Their total current scores are respectively `4,-2,4,-3`. Hence the sum-repaired
head scores add to `3`, while the average-repaired scores add to `-2/3`.
The four actual top kernels add to zero by the head-exchange identity. Both
repairs therefore fail as assignments on the full two-component kernel
algebra. The canonical five-label exact-grid and seven-label modular gates
also fail, but the head-exchange counterexample alone is decisive for the
proposed extension.

The independent `overnight_uniform_pruning_edge_current_repair_check.py`
enumerates literal oriented-edge slides by breadth-first search, verifies
equal normalized heads throughout each slide orbit, and computes signed
counts using all 120 permutations. It shares neither the producer's
reachability formula nor its signed subset recurrence.

Reproduction:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/overnight_uniform_pruning_edge_current.py
python3 research/sN/trees/overnight_uniform_pruning_edge_current_check.py
```

The first test reuses the saved exact five-label matrix and modular seven-label
matrix. The independent checker imports neither matrix nor a Fourier evaluator;
it checks normalized heads directly and recomputes signed counts by all vertex
orders. The exact five-label whole-function counterexample is decisive; the
seven-label modular failure adds no stronger claim.
