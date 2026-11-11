# A simpler restriction argument using fixed adjacent pairs

## Status and scope

This is a complete mathematical replacement for the random-rank, run-counting,
and isolated-gap-concentration part of the quadratic-width argument. The
matching Laplace inequality already has a Lean proof in the existing library;
the new fixed-pair assembly has not yet been formalized in Lean. The argument
below uses the five-input obstruction H(5,2) as a separately proved structural
lemma. It does not replace that lemma or its finite certificate.

The intended paper theorem is

> For every fixed C>0 there exists c_C>0 such that every ordinary two-hidden-layer
> ReLU network with arbitrary real biases computing MAX_N exactly on all of R^N,
> with h_1<=C N^2 and N>=3, satisfies h_2>=c_C N^2.

The proof obtains the stronger order N^2/max(1,C) for sufficiently large N
depending on C. The finite range is absorbed using h_2>=1. Consequently the
paper proof need not use the separate linear second-width lower bound. The
explicit Lean theorem retains its stronger uniform constant
1/(175000 max(1,C)) for all N>=3.

## Input supplied by normalization and half restriction

Let n>=10. Write a homogeneous normalized network as

    F(x) = l_0(x) + sum_j d_j sigma(a_j dot x) + sum_k v_k sigma(g_k(x)),
    g_k(x) = l_k(x) + sum_j w_kj sigma(a_j dot x),

where every a_j and every inner linear form l_k, k>=1, has coordinate sum
zero. The output linear form l_0 carries the unit translation slope of MAX.
These auxiliary linear forms and shallow output terms are allowed in the
proof's intermediate model; the original theorem concerns a network without
skips. Normalization and restriction retain the original second-layer index
set.

Suppose F=MAX_n and put

    r_j = |supp(a_j)|,
    M = #{j:r_j>=3},
    L = sum_j (r_j)_4,
    Q = sum_{j:r_j>=3} r_j^4.

Thus M<=Q and L<=Q. The separate elementary half-restriction lemma supplies
Q<=A C n^2 for an absolute A after replacing C by max(1,C).

The only structural input used below is H(5,2): every translation-normalized
exact MAX_5 network whose nonlinear first-layer rows have support at most two
has a second-layer preactivation whose summed signed pair-interaction graph
contains two disjoint edges. Linear terms are permitted by this lemma.

## Fixed small gaps

Fix an integer J with 1<=J<=m/2, where m=n-5. Choose a uniform random permutation
of the n coordinate labels. The first five labels form a set S and will all
receive input value zero. Place the remaining labels in tail positions
1,...,m, in the order given by the permutation.

Pair tail positions

    (1,2), (3,4), ..., (2J-1,2J).

The anchor is position 0 with value zero. Give gap r, between positions r-1
and r, a distinct power T^{kappa(r)}. Assign exponents 1,...,J to the even
gaps 2,4,...,2J and exponents J+1,...,m to all other gaps, in any fixed order.
The tail values are

    y_t = -sum_{r<=t} T^{kappa(r)}.

Every paired gap is smaller in asymptotic order than every gap between blocks.
In particular the anchor gap is large. There is no random gap ranking and no
event asserting that enough small gaps are isolated: all J chosen gaps are
isolated by construction.

Choose T once for the whole finite experiment. First take T large enough that
every first-layer row, under every label permutation, has the sign of the
highest-degree nonzero coefficient of its gap polynomial. After these signs
stabilize, each g_k at each permuted point is a fixed polynomial in T. Increase
T beyond the roots of every nonzero such polynomial. Therefore, in every
configuration,

    g_k(y)=0  implies  its entire tail coefficient vector is zero.       (1)

Indeed, if g_k equals b dot x_tail on the relevant tail cone, its gap polynomial
is -sum_r (sum_{t>=r} b_t) T^{kappa(r)}. Distinct exponents force all suffix sums
to vanish when the polynomial is identically zero; subtracting neighboring
suffix sums gives b=0. Rows supported wholly on S contribute zero on the tail
subspace and cause no differentiability problem there.

## Two combinatorial bad events

Let P denote the matching of J coordinate-label pairs in the chosen tail
slots. Declare a support T_j=supp(a_j), with |T_j|>=3, bad if either

1. it contains both endpoints of two distinct pairs in P; or
2. it contains both endpoints of a pair in P and two distinct labels of S.

Call the union of these events B_pair. This event depends on unordered pairs,
so it is invariant under independently swapping the endpoints of every pair.
Let B_selected be the event that a support of size at least three is wholly
contained in S.

Uniform-label counting gives

    P(B_selected) <= 60 M/(n)_3,                                      (2)
    P(B_pair) <= L [J(J-1)/2 + 10J]/(n)_4.                            (3)

For (2), fix any three labels of each eligible support. Their probability of
all belonging to S is (5)_3/(n)_3. For (3), there are binom(J,2) choices of two
pair slots and J binom(5,2)=10J choices of one pair slot and two selected
positions. For each choice, the four distinct labels belong to a given
support of size r with probability (r)_4/(n)_4. Sum over slots and rows.
Overlaps between witnesses cause no problem because this is a union bound.

## Why good pairings make all non-braid gates invariant

Consider a zero-sum row a, holding fixed S, the unordered labels in each pair,
and all singleton labels. Its large-gap coefficients are unchanged by every
endpoint swap. If any such coefficient is nonzero, the chosen large T makes
the row's activation sign independent of all swaps.

Suppose instead every large-gap coefficient vanishes. The zero suffix sums at
block boundaries imply that every singleton coefficient is zero, that the
two coefficients within every pair add to zero, and that the coefficients on
S add to zero. If a has a nonzero tail coefficient, at least one pair has two
nonzero opposite coefficients. If two such pairs exist, its support witnesses
the first bad event. If exactly one exists and |supp(a)|>=3, there is at least
one nonzero coefficient on S; their zero sum forces at least two, witnessing
the second bad event. Thus outside B_pair every row of support at least three
is either supported wholly on S or has an activation sign invariant under
all pair swaps.

For a row of support two, zero coordinate sum means a=alpha(e_u-e_v). Such a
row's sign changes only if {u,v} is one of the J matched pairs; all other pairs
of labels have a fixed order, including pairs with an endpoint in S.

## The fair-coin estimate for a fixed second neuron

For each second neuron k, combine all first-layer rows with support {u,v}.
After orienting them using sigma(-t)=sigma(t)-t, write their combined nonlinear
part as

    c_{k,uv} sigma(x_u-x_v),
    c_{k,uv} = sum_{j:supp(a_j)={u,v}} w_kj |a_{j,u}|.

Let G_k be the graph having edge {u,v} exactly when c_{k,uv} is nonzero. These
are the actual summed signed coefficients; opposite contributions may cancel.

Conditional on S, the unordered pair labels, and the remaining tail order,
the J pair orientations are independent fair bits. Outside B_pair, the tail
coefficient vector of g_k has the form

    b_k + sum_{i=1}^J epsilon_i c_{k,u_i v_i}(e_{u_i}-e_{v_i}),          (4)

with a suitable fixed orientation convention. The vectors for nonzero
coefficients have disjoint supports and are therefore linearly independent.
If X_k counts matching pairs that are edges of G_k, at most one setting of
those X_k bits can make (4) zero. Using (1),

    P(g_k(y)=0 and not B_pair | unordered configuration) <= 2^{-X_k}. (5)

The right side can still be used on a bad unordered configuration because
the event on the left is then empty. Thus no independence between B_pair
and G_k or between B_pair and the matching is assumed.

## A short matching Laplace lemma

For any graph G with e edges on m vertices, if P is a uniform J-matching and
X=|P intersect E(G)|, then

    E[2^{-X}] <= exp(-J e/(2m^2)).                                   (6)

A self-contained proof is in matching/lemma.tex. Briefly, force a fixed edge
ab into the first pair of a uniform permutation by two position swaps. The
result has the conditional matching law given ab in P, and changes at most
three pairs. For F(z)=E[z^X] and mu=2Je/[m(m-1)], this coupling gives

    F'(z) >= mu z^2 F(z),  0<z<=1.

Integrating from 1/2 to 1 yields the stronger exponent
7Je/[12m(m-1)], which implies (6). This argument requires neither independent
edge indicators nor a concentration theorem.

## Per-neuron coverage costs O(J^{-2})

Fix k and let e=|E(G_k)|. The probability that S contains two disjoint graph
edges is at most

    (e^2/2) (5)_4/(n)_4 = 60e^2/(n)_4.                              (7)

After S is fixed, the tail matching is a uniform J-matching on m labels. The
tail graph has at least e-5(n-1) edges. From (5) and (6), the probability that
the neuron is zero, the pairing is good, and S contains the required two
edges is therefore at most

    [60 e^2/(n)_4] exp(-J[e-5(n-1)]/(2m^2)).                         (8)

The bound remains valid if e-5(n-1)<0: then the exponential upper bound is
merely larger than one. Since m=n-5>=n/2 and J<=m/2, the positive shift in the
exponent is bounded by an absolute constant. Also (n)_4>=n^4/2 for n>=10.
Putting u=Je/(2m^2), the remaining factor is an absolute multiple of

    J^{-2} u^2 exp(-u).

The function u^2 exp(-u) is bounded on [0,infinity). Thus (8) is at most D/J^2
for an absolute D, independently of the graph, all network coefficients,
and the widths. This includes the empty graph, for which (7) is zero.

## Covering the good configurations

Outside B_selected, localization at y on the five tied coordinates has no
non-braid nonlinear first-layer row. Indeed, genericity implies that a
first-layer row vanishes at y exactly when its support is contained in S.
The localized network computes MAX_5. Apply H(5,2).

An original second neuron whose preactivation is nonzero at y contributes
linear and shallow first-layer terms, or zero, under localization. It supplies
no retained outer ReLU in the localized model. The matching witness furnished by H(5,2) must
therefore be an original neuron with g_k(y)=0, and its two disjoint edges are
the original edges of G_k induced by S. No new second-layer neurons are charged.

Every configuration outside B_selected union B_pair is therefore counted by
at least one of the events bounded in (8). Combining the bounds gives

    1 - 60M/(n)_3 - L[J(J-1)/2+10J]/(n)_4 <= D h_2/J^2.              (9)

This is the entire counting inequality needed for the existential theorem.

## Closing the existential theorem

Suppose Q<=A C n^2 with C>=1. Choose a sufficiently small absolute delta>0,
depending only on A, and let J=floor(delta n/sqrt(C)). For all sufficiently
large n depending on C, J>=delta n/(2sqrt(C)), 1<=J<=m/2, and the two error
terms in (9) have sum at most 1/2: the first is O(C/n), the second is
O(C J^2/n^2)=O(delta^2), with a vanishing O(CJ/n^2) term.

It follows that

    h_2 >= J^2/(2D) >= delta^2 n^2/(8DC).

The half restriction has n=floor(N/2), hence n>=N/3 for N>=3. This proves a
quadratic bound for all sufficiently large N, with C fixed. For the finite
remaining range, h_2>=1 because a network with no second neurons is constant
in the ordinary no-skip architecture. Decrease the positive constant to
cover those finitely many N. The result is exactly the existential-constant
paper theorem stated at the beginning.

## Simplification routes considered

1. **Fixed isolated small gaps: DIRECT_REPLACE.** The argument above removes
   random ranks, run enumeration, all isolated-gap probability estimates,
   and their first/second-moment analyses. It preserves the quadratic exponent.
2. **Coarse half-support moment: DIRECT_REPLACE.** A single expectation of
   sum r^4 replaces separately optimized joint budgets for M and L.
3. **First moment instead of second moment for old ranks: SUPERSEDE.** This
   already suffices for an existential constant, but fixed pairs remove both.
4. **Generating polynomial instead of size-bias terminology: DIRECT_REPLACE.**
   The same elementary pinning coupling yields (6) in one calculation.
5. **Independent random edges: REJECT.** They need not form disjoint swaps,
   so their gradient columns need not be independent. Collision deletion
   reintroduces complexity; star graphs expose the dependence immediately.
6. **Greedy large graph matching: REJECT for this exponent.** An edge-rich
   star can have matching number one, so an arbitrary matching extracted
   deterministically cannot supply exponential decay in total edge count.
7. **Use h_2>=1 for finite arities: DIRECT_REPLACE for the requested quantifiers.**
   This removes the separate linear lower bound from the paper proof. It
   intentionally gives an unspecified c_C, not a uniform explicit c/C for
   every finite N.
8. **One generic tail point with no pair flips: KEEP AS INSUFFICIENT.** It
   supplies the structural witness but no uniform per-neuron probability.
   The fair orientation bits are what make arbitrary signed weights manageable.

## Lean correspondence and remaining work

Existing normalized-model and H(5,2) theorems supply the semantic ingredients.
The matching estimate is already verified in
MaxCaterpillar/Frontier/RandomRestriction/MatchingSizeBias/Laplace.lean.
The fixed-pair bad-event estimate, swap-invariant gate lemma, and their
assembly are new paper-level arguments in this note, pending Lean proofs.
They have passed the independent mathematical audit in
../fixed_pairs_audit/AUDIT.md, including signed and zero-boundary cases.
The former random-rank Lean proof remains the verified source of the
explicit constant theorem.
