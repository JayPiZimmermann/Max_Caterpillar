# Independent audit of predetermined small-gap pairs

Status: the mathematical fixed-pair argument passes the independent audit
below. This is a written proof audit, not a Lean verification of the new
sampling construction. The already verified five-input structural theorem
is still a separate required ingredient; this audit does not remove its
finite certificate.

Auditor: `/root/clean_fixed_pairs_audit`. Reviewed independently of the
probability worker's implementation on 3 November 2026.

## Exact setting

Work after the proved homogeneous, translation-normalized reduction. Each
first-row covector has coordinate sum zero. A second preactivation is a
linear head plus a signed sum of first-row ReLUs, and its head also has
coordinate sum zero. The full output is

    F(x) = L(x) + sum_j B_j relu(A_j x) + sum_k d_k relu(g_k(x)),
    g_k(x) = U_k(x) + sum_j W_kj relu(A_j x).

The output head satisfies L(1)=1, whereas A_j(1)=U_k(1)=0. In particular,
neither the shallow output terms nor the translation slope of L may be
dropped. This intermediate class is allowed even when the original public
theorem concerns ordinary networks without skips.

Let n=m+k. Choose k selected labels uniformly and put their base coordinates
at zero. Arrange the other m labels uniformly in ordered tail positions
1,...,m, whose coordinates are negative and strictly decreasing. Fix J
pairwise disjoint adjacent pairs of tail positions. In particular, the
anchor-to-first-tail gap is never a pair gap. Give the pair gaps distinct
exponents 1,...,J, and every other gap a distinct exponent greater than J.
The gaps are powers B^r. A sufficiently large common B is chosen after the
finite network and the finite sample space are fixed.

Let R be the support of a first-row covector. Declare its support bad when:

* it contains the four endpoints of two chosen tail pairs; or
* it contains both endpoints of one chosen tail pair and two selected labels.

Also exclude, separately, every non-braid row whose whole support is
selected. Here a non-braid row has at least three supported coordinates.

## 1. The signed gate argument is valid

The coefficient of a gap in a zero-sum row's value is the sum of the row
weights above that gap; equivalently it is minus the sum below it. Reversing
the labels inside one adjacent pair changes only the coefficient of that
pair's small gap. Thus every coefficient of every large gap is unchanged
under all pair reversals.

Suppose all large-gap coefficients vanish. Collapse each chosen pair to one
block and leave all other tail positions as singleton blocks. The anchor
gap is large, so the sum of the selected weights is zero. Differences of
successive large-gap coefficients show that every tail block has total
weight zero. Hence every singleton weight is zero and the two weights in
each pair are opposites.

Now suppose the row has tail support and has at least three supported labels.
There is a pair with two nonzero weights. If another pair has nonzero
weights, the first bad event holds. Otherwise the row has at least one
nonzero selected weight; its selected weights sum to zero, so it has at
least two nonzero selected weights. The second bad event holds.

Consequently, outside the support-bad event, every non-braid row with tail
support has a nonzero large-gap coefficient. Its highest nonzero such
coefficient is invariant under all pair reversals and dominates every
smaller exponent for sufficiently large B. Its sign, and therefore its
ReLU activation gate, is constant on the entire pair-reversal cube.

This proof uses neither positive row weights nor a generic-position
assumption on them. Cancellations of selected weights, opposite pair
weights, and zero large-gap coefficients were all included explicitly.

## 2. The support-error estimate has the stated factors

Write L=sum_j (|R_j|)_4, with falling factorials. For one fixed set of four
positions, the probability that their distinct labels all lie in R_j is
(|R_j|)_4/(n)_4. There are binom(J,2) choices of two tail pairs and
J binom(k,2) choices of one tail pair and two selected positions. Thus

    P(support bad) <= L [binom(J,2) + J binom(k,2)] / (n)_4.

For k=5 the second coefficient is 10J. This argument is a union bound, so
overlapping witnesses cause no problem. If M counts the non-braid rows,
the whole-selected event has probability at most

    M (k)_3/(n)_3.

The latter estimate follows because a row of support size r>=3 has
containment probability (k)_r/(n)_r, which is zero for r>k and otherwise
at most (k)_3/(n)_3.

Both error events depend only on the selected set and the unordered pairs,
not on their orientations. Conditioning on their complements therefore
does not introduce a bias among the pair-reversal bits.

## 3. Zero preactivation forces zero tail gradient

For any fixed sample, signs of all first preactivations stabilize as B tends
to infinity. On that stabilized region a second preactivation at the base
point is a polynomial in B, namely a linear combination of the distinct gap
powers. There are finitely many samples and neurons. Choose B beyond all
sign-stabilization thresholds and all positive roots of their nonzero
polynomials. Then a second preactivation that vanishes at the base point
has every gap coefficient zero.

The change from tail coordinates to consecutive gaps is invertible, so all
tail-coordinate coefficients vanish. These coefficients are precisely the
tail gradient. First rows supported entirely on the selected labels may be
nondifferentiable in selected directions, but are constant in all tail
directions; they do not obstruct this statement.

The common-B choice is important. Choosing a different B depending on the
pair-reversal bits would invalidate the following cube count. Finiteness
provides one B that works for every orientation and every sample.

## 4. The flip columns have disjoint supports

Fix the selected set, the unordered chosen pairs, and all other tail data.
On the good event, non-braid first-row gates are fixed. A braid first row
involving two labels that are not the endpoints of the same chosen pair
also has fixed ordering. Therefore reversing one pair {a,b} changes the
tail gradient of a second preactivation only by

    c_ab (e_a-e_b),

up to an immaterial common orientation convention. Here c_ab is the sum of
the signed contributions of all original first rows on that same pair.
Thus parallel-edge cancellation is included before defining the graph
G={ {a,b}: c_ab != 0 }.

The gradient is an affine function of the independent reversal bits, and
its nonzero columns have disjoint coordinate supports. If X chosen pairs
are edges of G, then at most one assignment to those X bits can make the
gradient zero. The fraction of all orientations with zero preactivation is
therefore at most 2^(-X).

There is no assertion of scalar anti-concentration for arbitrary signed
coefficients here: the vector-valued gradient and disjoint column supports
are essential.

## 5. The matching estimate and selected event combine correctly

Given the selected set S, the chosen tail pairs form a uniform J-matching
on its m remaining labels. The elementary pinning-coupling proof in
`../probability/matching/argument.md` gives

    E 2^(-X) <= exp[-J e_tail/(2 m^2)].

Its three-pair damage bound and conditional matching law were checked:
pinning a fixed graph edge to the first slot gives a uniform matching
conditioned on containing that edge, after slot order is forgotten. The
generating-function inequality has the correct direction for 0<z<=1.

If G has e edges, deleting the k selected vertices removes at most kn
edges. Thus e_tail>=e-kn, uniformly in S. Also, by a union bound over two
disjoint graph edges,

    P(G[S] contains a two-edge matching) <= (e^2/2) (k)_4/(n)_4.

Consequently the probability that this neuron both survives and supplies
the selected matching witness is at most

    (e^2/2) (k)_4/(n)_4 * exp[-J(e-kn)/(2m^2)].

For fixed k, m=n-k, and 1<=J<=m/2, this is O_k(J^(-2)). To see it directly,
put a=J/(2m^2), factor out exp(a kn), and use
e^2 exp(-a e)<=2/a^2, which follows from exp(t)>=t^2/2. The factor exp(a kn)
is bounded independently of n,J when n>=2k; also m^4/(n)_4 is bounded once
n is bounded below by a fixed constant. No independence between the selected
matching event and tail graph density is assumed.

## 6. Actual-network obligations that remain visible

The local model at a tied base point retains a second-hidden neuron only
when its original preactivation is zero. On a sample without a wholly
selected non-braid row, its remaining nonlinear first-row functions are
scalar coordinate differences. Non-braid rows with fixed gates contribute
only to linear heads. The interaction graph on the selected labels is
therefore exactly the induced graph G[S], with the original second-neuron
index unchanged.

The structural theorem H(k,2) is what ensures that some retained original
second neuron has two disjoint selected edges. It cannot be replaced by
merely requiring a nonzero mixed difference of a single neuron: that weaker
criterion has known star counterexamples of capacity order 1/n.

The full first-layer regularization and the proof of H(k,2) are separate
obligations. Given those, this fixed-pair argument genuinely replaces the
random rank permutation, isolated-gap counting, and concentration estimates.
It does not merely rename them.

## 7. Combined normalization and fixed-pair model audit

The parent identified an earlier draft mismatch: the probability fragment
omitted shallow output terms and described the output linear head as
translation invariant. That draft is not the version approved here. The
corrected `../probability/fixed_pairs.tex` and
`../normalization/normalization.tex` were read together and checked against
the actual Lean definitions in
`MaxCaterpillar/Frontier/RandomRestriction/NormalizedNetwork/Model.lean`
and `GrowingMatching/Structural.lean`.

The diagonal normalization of an ordinary homogeneous network is faithful:
outer gates positive at the diagonal contribute their entire inner
directional derivative, which includes both a linear head and shallow
first-row ReLUs. Gates zero there retain their original outer slots; gates
negative there disappear. The surviving first rows have zero sum. The
inner linear head of a retained outer gate has value equal to the gate's
original value at the diagonal, namely zero. The aggregate output linear
head has value one. This gives exactly the full model above, with at most
the original first and second widths.

For a coordinate restriction S, choose an anchor a in S and set

    (H_S y)_i = y_i for i in S, and y_a for i outside S.

Then H_S 1_S = 1_N. At a base point q that is zero on S and strictly
negative outside, MAX_N(q+epsilon H_S y)=epsilon MAX_S(y) for every
epsilon>0. When a first gate has nonzero value at q, its derivative is
linear or zero; otherwise its whole covector is supported in S and its
nonlinear derivative is the original restricted row. Every absorbed
linear contribution A_j H_S still has zero sum, as does U_k H_S. Thus each
retained inner head is normalized automatically. The output head L H_S
still has value one; all other contributions have zero translation slope.

No new outer neuron is created. An outer gate positive at q contributes a
linear head plus shallow terms, while one negative at q contributes zero.
These are placed in L and B, respectively, not recompiled into extra outer
ReLUs. Removed original indices can be retained as zero slots.

On a good fixed-pair sample, all surviving nonlinear first rows are
supported on two selected labels. Their coefficients W_kj are unchanged
for each retained original outer slot. Consequently its summed signed
interaction graph is exactly the induced ambient graph G_k[S]. Absorbed
linear heads, including anchor-coordinate contributions from H_S, create
no interaction edges. Original shallow output terms and the derivatives
of positive outer gates remain shallow braid functions.

This matches the exact structural hypothesis `LocalMatchingObstruction`:
it is quantified over `NormalizedNetwork`, whose `eval` explicitly includes
the shallow B_j terms. Hence applying H(5,2) after this restriction is valid
without assuming a stronger obstruction for a narrower model or counting
auxiliary heads as original second-layer neurons.

The combined-model verdict is **PASS for the corrected manuscript
fragments**. The current fragments use different label names for the
regularization lemma; that is an editorial cross-reference issue, reported
to their author, rather than a mathematical hypothesis discrepancy.

## Reproducible finite control

Run `python3 control.py` in this directory. The independent integer test
enumerates 8,050 zero-sum non-braid rows in {-2,-1,0,1,2}^7, using three tied
coordinates and two tail pairs. For the 1,612 good tail-supported rows, all
four pair orientations have identical nonzero sign and identical large-gap
coefficients. Six wholly selected rows are correctly separated. The test
uses exact integers and has status PASS in `control.json`; it supplements
the universal argument above and is not presented as its proof.

## Audit verdict

**PASS as a mathematical proof of the fixed-pair probabilistic replacement.**
No failure was found in the signed, cancellation, orientation, anchor, or
conditioning cases. A new Lean formalization of this shorter sampling
construction is still required before calling this replacement Lean verified.
