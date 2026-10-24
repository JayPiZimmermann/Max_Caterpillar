# Overnight all-tree lower-bound search, 24–25 October 2026

The unrestricted exponential lower bound remains open. The seven-label
matching separator now has an exact finite rational certificate (113 rows,
258 full permutation-orbit columns, ranks 112/113), and its independent
coverage/arithmetic checker passed. The resulting unrestricted bound is
`|K| >= binom(N,4)/35` for `N>=7`. This is a mathematical proof with an
exact finite certificate; no Lean result is claimed.

## Seven-label separation and a quartic bound

The certificate separates the maximum from all full canonical tree units
whose six-vertex nonapex tree has matching number at most two, modulo `L_5`.
It allows every head root and every edge orientation. Missing or linear
edge states lie in `L_5` at this arity and do not alter the statement.

The producer uses cut components away from the head root. It chooses 113
independent augmented rows modulo 1000003, then computes all orbit sums with
integer common denominators. An integer left-kernel vector annihilates all
258 exact columns and has a nonzero target value. Modular evidence is used
only to select rows; all claimed separation is checked over the rationals.

The independent checker enumerates all 1296 labelled six-vertex trees by
Prüfer sequences, checks the matching filter by disjoint edge triples,
exhausts every head root and orientation, and verifies coverage after
normalizing the head. It recomputes every row from positive-endpoint cuts
and their normalized head sums, then checks the integer dot products. It
imports neither the producer nor a linear-algebra solver.

Consequently, for every canonical tree-face expansion of
`max_N` with the paper's auxiliary remainder and `N>=7`,

\[
\boxed{|K|\geq\frac{\binom N7}{\binom{N-4}3}
             =\frac1{35}\binom N4
             =(1/840+o(1))N^4.}
\]

The finite separator alone is not a counting argument. The bridge is as
follows. At each seven-label top tie, freeze all other coordinates at
sufficiently separated negative integer powers. The existing canonical-head
germ lemma forces the apex of any relevant unit into the tie. Its six other
tied labels form a connected induced subtree of its original tree, every
edge of that subtree is retained as a hinge, and the transported head is
again canonical. The auxiliary functions and every lower-dimensional germ
vanish in the top quotient. Applying the separator to the germ identity
therefore forces some contributing tree on those six labels to have a
perfect matching.

Assign to each tie one such unit and its perfect matching. For a fixed unit,
the three matching edges recover their six endpoints and the unit's fixed
apex recovers the entire tie set. This is an injection into the size-three
matchings of the original tree; no root or ordering factor occurs. In fact
a forest has at most one perfect matching on any prescribed vertex set.

For an `n`-vertex forest, let `m_k` count its size-`k` matchings. Then

\[
m_k\leq\binom{n-k}{k}.
\]

Proof: remove an isolated vertex if present. Otherwise take a leaf `v`
with neighbour `u` and partition matchings according to whether they use
`uv`. The recurrence is
`m_k(F)=m_k(F-v)+m_(k-1)(F-{u,v})`. Induction and Pascal's identity give
the bound. The empty matching and `n<2k` are immediate boundary cases.
For `n=N-1,k=3` the bound is `binom(N-4,3)`, yielding the displayed result.

The stronger weighted statement is

\[
\sum_{j\in K}m_3(T_j)\geq\binom N7.
\]

Thus original trees of matching number at most two contribute zero and
can be allowed without counting them in this lower bound. The old cubic
bound remains useful at small arities; take the maximum of the two bounds
where both apply. Neither bound allows arbitrary real head vectors,
arbitrary real edge coefficients, or cyclic graphs.

Both the unrestricted-width agent and the construction agent independently
reviewed the tie-to-matching injection and the forest counting argument.
The independent arithmetic/coverage check is recorded separately.

The check completed in 230.30 seconds with exit status zero. It verified
all 113 rows, all 1296 labelled six-vertex trees (576 with matching number
at most two), all 768 allowed root/orientation choices on the four allowed
unlabelled shapes, and the resulting 158 distinct function orbits represented
by the 258 columns. The integer target value is nonzero (7041 decimal digits).

## Broader exponential mixtures: all matching-number-two units are free

Coordinate deletion propagates the seven-label separator to every arity
`m>=7` for the fixed class of trees with matching number at most two.
Deleting a leaf cannot increase the matching number; deleting an apex or
internal vertex vanishes in the next top quotient. The existing canonical
head-transfer and face-state arguments apply without an orientation
restriction.

Let `B` be the caterpillar/rooted-star face dictionary (also allowing the
reviewed arbitrary-shape full source/root units). Adjoin all arbitrary
tree-face units with original matching number at most two, with every root,
orientation and face state. Assign these added functions to a free class
before counting. For `N>=7`, the remaining terms satisfy

\[
Z\geq\frac{(7/6)^N}{(N+1)^6}.
\]

If arbitrary tree-face units with original matching number at least `k`
are additionally allowed, where `0<=2k<=N-1`, then

\[
Z\geq\frac{(169/147)^k}{(N+1)^6}.
\]

These are the existing star-extension proofs with ties starting at seven
rather than five. For the first bound, weight an `m`-tie by `6^(-m)`:
`(7/6)^N-sum_(j=0)^6 binom(N,j)6^(-j) <= (N-6)Z`. The separator gives
`Z>=1`, and the low-degree terms are absorbed by `(N+1)^6`.
For the second, set `y=2/11` and use the existing mixed matching estimate
with `rho=147/169`. Its factor `E=(13/11)^N rho^k` is at least one.
The final coefficient is at most
`sum_(j=0)^6 N^j + N-6+2(N-1)/13 <= (N+1)^6`.
This extension is independently reviewed mathematically; it is not Lean
verified. It includes arbitrarily oriented double stars, not just stars.
Nonstar classes of growing but sublinear matching number remain open.

## Uniform separation remains the main residual

The odd-arity perfect-matching separation hypothesis in `reopen_lower_odd.md`
would yield the unrestricted exponential base `2/phi`. One fixed odd arity
only yields a polynomial bound. More generally an exact separator at
`m=2q+1` gives

\[
|K|\geq\frac{\binom N{2q+1}}{\binom{N-q-1}q}
       =\frac{\binom N{q+1}}{\binom{2q+1}q},\qquad N\geq2q+1.
\]

The next discriminating finite case is nine labels and eight-vertex trees
without perfect matchings. A size/coverage inventory will precede any
long numerical run. A family of finite separators must not be promoted
to an all-arity theorem without a uniform proof.

The nine-label inventory now has an independent complete-domain check:
all 262144 labelled eight-vertex trees, all 23 unlabelled shapes, all 18
matching-deficient shapes, and all 3822 normalized function orbits are
covered. The checker uses Prüfer sequences and coloured-tree canonical
forms, sharing no graph-library enumeration or isomorphism code with the
producer. This certifies the search domain only. A cached subset dynamic
program for full permutation-orbit sums is being developed before launching
the rank search; there is no nine-label separation claim yet.

## A paired-frequency shortcut, and its obstruction

For odd `m=2q+1`, consider frequencies tending to
`(0,z1,-z1,...,zq,-zq)` with direction `(2q,-1,...,-1)`.
If a unit's apex is the zero-frequency label, a cut sum vanishes in the
limit exactly when its component is a union of whole pairs (choose generic
`z`). There can be `q-1` such cuts only if the chosen pairs are actual
edges of the tree: deleting those cuts leaves `q` connected two-vertex
components. Without that perfect matching there are at most `q-2` such
cuts, and the numerator's order `2q-3` makes the unit vanish at least
linearly. A matching unit can instead contribute a `t^(-1)` coefficient.

This observation does **not** give a separator for units with variable
apex. The exact test `overnight_lower_pairlimit.py 5` finds a star with
nonzero symmetric `t^(-1)` coefficient `69407/326700`, while the maximum
has coefficient `1/400`, at base frequencies `(0,1,-1,10,-10)`.
The candidate single functional therefore fails already at five labels.
The useful residual is how to cancel contributions from other apex labels
without also killing the maximum; fixed-coordinate residue/deletion alone
is already known to be insufficient. This refutes this shortcut only.

## Reproduce the exact seven-label gate

From the repository root, using the existing research Python environment:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 1250s research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/overnight_lower_matching_exact.py rows
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 1250s research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/overnight_lower_matching_exact.py solve
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 1250s research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/overnight_lower_matching_check.py
```

Each phase has an internal 1200-second budget and uses one computation
thread. Exact rows, row scales, integer weights, logs and content hashes
are adjacent to the scripts. The producer checkpoints after every row.
