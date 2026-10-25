# Full label symmetrization does not repair the anchored six-flag lift

This is an exact counterexample to the specific actual flag lift in
overnight_uniform_flags_transfer.md, including its full \(S_9\) average.
The operator has the correct filtration drop. Its matching vanishing fails.
Stop this lift; this result does not exclude other flag/tensor constructions.

Use apex \(0\), root \(1\), and the inward tree

\[
 (2,1),(3,2),(4,3),(5,1),(6,1),(7,1),(8,1).
\]

It has eight nonapex vertices and matching number two.
Follow the six-flag block transfer by the certified symmetrized five-label
separator. The unaveraged full \(S_9\) scores are

\[
 -864000\quad\text{on this tree unit},\qquad
 -43545600\quad\text{on }\max_9.
\]

The control does not enumerate millions of long flags. It exhausts the
126 possible sets of five retained labels:

| Retained-set class | Count | Reason for its contribution |
|---|---:|---|
| Original apex removed | 56 | The zero fiber is a point; other fibers are zonotopes |
| Apex retained, induced tree disconnected | 55 | Every relevant fiber has dimension at most three |
| Apex retained, induced four-vertex star | 10 | The certified base separator vanishes |
| Apex retained, induced four-vertex path | 5 | Nonzero contribution below |

For the five path cases the retained nonapex set is
\(\{1,2,3\}\) together with one element of \(\{4,5,6,7,8\}\).
All four deleted vertices are leaves. Therefore their block projection is
the cube, in every ordering, and its zero-fiber transfer coefficient is
\(-1\) for the weighted six flags.
Every retained path is an inward canonical path. The normalized head
invariant is \(\kappa_v=1\) at every vertex, so its base separator value is
the same \(60\), independently of the root's position after relabeling.

Each retained set occurs with \(5!\) retained-label orders and \(4!\)
deleted-label orders. Consequently its total contribution gives

\[
 5\cdot5!\cdot4!\cdot(-1)\cdot60=-864000.
\]

The unsymmetrized target value is \(-120\), giving
\(9!\cdot(-120)=-43545600\).

The zero-fiber arguments use the actual complete face operations.
A complete block flag fixes every deleted coordinate separately.
Any tree generator touching a deleted vertex is fixed at an endpoint,
while only edges within the retained set can remain free.
If the apex does not lie in the selected projected fiber, that fiber is
a zonotope. These facts justify every zero entry in the table.

overnight_uniform_flags_sym.py is a standard-library checker.
It re-enumerates every retained set, checks the induced-tree classification,
computes the zero-vertex coefficient directly from signed lexicographic
normal-cone membership, and recomputes the base path/star/simplex values
by vertex maxima and minima. It imports no Fourier or matrix code and
does not import the earlier transfer producer.
