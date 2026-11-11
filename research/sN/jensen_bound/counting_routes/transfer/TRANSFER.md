# Verified conditional growing-arity transfer

The finite actual-network transfer, explicit braid finite-q and square-root
corollaries, explicit normalized general-row corollary, and raw affine-skip
general-row wrapper are Lean verified with independent exact-type and ordinary
axiom audits. Their structural hypothesis H is explicit and remains unproved
at growing orders. No unconditional exponential lower bound or quadratic
upper bound is asserted.

The braid consequence has growth exp(c*sqrt(n)): a stretched exponential, not
exp(c*n). The general-row consequence has conditional growth
exp(c*n^(1/3)*log(n)) for fixed quadratic first-width budget.

## The open structural hypothesis

`LocalMatchingObstruction(k,q)`, abbreviated H(k,q), states that every actual
homogeneous translation-normalized skip network for MAX_k, with every first
row supported on at most two coordinates, has an original second neuron whose
actual interaction graph contains q disjoint edges. All coefficients are
arbitrary reals, and the braid one-layer output and linear skips are allowed.
The graph uses the summed signed pair coefficients, including all parallel-row
cancellations. H contains no width, probability, rank or random-restriction
premise.

Jensen's SC'_(2q-1), at k=4q+1, implies H(k,q). Indeed, the endpoints of a
maximal matching cover every edge, so matching number at most q-1 gives vertex
cover at most 2q-2. Such a neuron lies in K_(2q-2), hence in C_(2q-1).

The verified calibration H(5,2) follows from the closed all-real star/triangle
certificate. It does not establish the growing hierarchy. A separate actual
MAX1 countermodel verifies that H(1,1) is false. Upward arity monotonicity of H
is proved by actual generic localization and ambient matching transport,
without graph contraction.

## Finite actual-network transfer

Let an actual normalized real network compute MAX_n, with n=m+k. Let

    M = number of original first rows with support at least3,
    L = sum_j (r_j)_4,

where r_j is the original support cardinality and (x)_r is the falling
factorial. Output-only first rows are included in these statistics. Suppose
m>=2, k>0, q>0, 4<=K<m and n>=4. Put

    c = 7K/[24m(m-1)],
    B1 = M (k)_3/(n)_3,
    B3 = L/(n)_4 * [ K^2(1+k/m)/(1-K/m) + (k)_2 K/2 ].

Under H(k,q), the verified finite inequality is

    1 - 8K/m - B1 - B3
      <= h2 * (k)_(2q)/(n)_(2q) * c^(-q) * exp(c*k*(n-1)).    (T)

A negative left side is harmless. The actual theorem derives its common
structured point and every event/rank/probability estimate. No genericity,
counting prerequisite, or assumed probability bound is a headline premise.
Its Lean declaration is `GrowingMatching.conditional_finite_transfer`.

### Why the preserved factorial matters

For an ambient graph G with eta ordinary unordered edges, a uniform k-set S
contains a q-matching only if it contains the 2q distinct vertices of one of
G's q-matchings. Ordering each q-edge set gives q! distinct lists, so

    P(S contains a q-matching)
       <= eta^q/q! * (k)_(2q)/(n)_(2q).

Condition on S and the gap ranks. On the long-isolated-gap event there are
J>=K/2 disjoint actual tail position pairs. The actual clean recording-fiber
rank theorem bounds joint clean survival by the uniform matching moment.
The bounded-size-bias coupling gives

    E_tail[2^(-X)] <= exp(-7J*tR/[12m(m-1)]) <= exp(-c*tR).

The same original graph induces the actual tail graph, and deleting k selected
vertices loses at most k(n-1) edges. This is a pointwise bound; selected and
tail graph events are not assumed independent. The per-neuron cost is at most

    (k)_(2q)/(n)_(2q) * eta^q/q! * exp(-c*eta+c*k*(n-1)).

One nonnegative exponential-series term gives

    exp(c*eta) >= (c*eta)^q/q!.

It cancels the preserved factorial and the eta power, including eta=0. No
Stirling estimate or optimization is needed. Discarding q! earlier would lose
the square-root parameter regime.

### The selected-arity dependence of the bad events

A first row of support at least3 is internal to S with probability at most
(k)_3/(n)_3, using one fixed three-element subset of that row. This gives B1.

The three original four-distinct-label role types have cardinalities
(r)_4/4, (r)_4/2, (r)_4/4. Their actual full-position lifts have factors
1, k and (k)_2. Pointwise there are at most2K oriented adjacent tail pairs at
selected gaps. The expected ordered same-run pair count is at most
2K/(1-K/m), and the expected anchored-run length is at most
K/[m(1-K/m)]. Thus a single row contributes at most

    A: (r)_4/(n)_4 * K^2/(1-K/m),
    B: (r)_4/(n)_4 * k*K^2/[m(1-K/m)],
    C: (r)_4/(n)_4 * (k)_2*K/2.

All terms share the actual full four-label denominator (n)_4. Their sum gives
B3. In particular, the selected-five constant is not reused when k grows.
The adjacent-pair count is bounded before taking the run expectation, so no
independence of overlapping gap events is assumed.

Outside these bad events and the short-isolated-gap event, actual localization
and H supply an original surviving neuron with the selected q-matching.
The finite event union over the original h2 indices proves (T).

## Explicit verified braid consequence

For a braid first layer M=L=0. If q>=1 and160000*q^2<=n, H(4q+1,q) implies

    h2 >= (23/25)*4^q.

The proof uses k=4q+1, m=n-k and K=floor(m/100), with all integer floors,
falling-factorial ratios, exponential shifts and support statistics derived.
The declaration is
`GrowingMatching.BraidCorollary.conditional_braid_integer_q_lower_bound`.

Consequently, for n>=160000 and q=floor(sqrt(n)/400),

    H(4q+1,q)  ==>  h2 >= (23/25)*4^floor(sqrt(n)/400).        (B)

The equality between the integer-square-root formula and the literal real
sqrt/floor expression is also verified. The declaration is
`GrowingMatching.BraidCorollary.conditional_braid_sqrt_floor_lower_bound`.
This is conditional exp((log4/400-o(1))*sqrt(n)), improving the conditional
power in Jensen's Corollary42. It does not prove H at those orders.

## Explicit verified general-row and original affine consequences

For integers d>=1 and q>=1, suppose

    n>=8000*d^2, 1000*d^2*q^3<=n,
    M<=d^2*n^2, L<=d^2*n^2.

Then H(4q+1,q) implies for the actual normalized MAX_n network

    h2 >= (1/2)*[n/(400000*d*q^2)]^q.                         (G)

The declaration is `GrowingMatching.conditional_general_rows`. It derives the
literal choice K=floor((n-(4q+1))/(1000*d)), the positive surviving fraction,
and its exact per-neuron envelope. For fixed d and q of order n^(1/3), this
has growth exp(c_d*n^(1/3)*log(n)); the finite inequality is the formal claim.

The raw affine-skip wrapper derives normalization and a half-size actual
network, retaining the original first and second index sets. For integer
C>=1, an original all-real MAX_N network with h1<=C*N^2 admits the verified
choice

    n=floor(N/2), d=20*C.

Under the same displayed integer size inequalities and H(4q+1,q), (G) bounds
the original h2. Every first slot is counted, including output-only rows.
No normalization or support-budget premise is left to the caller. The
declaration is
`GrowingMatching.AffineGeneralRows.conditional_affine_quadratic_width_lower_bound`.

## What is still open

The growing local structural obstructions remain the central unproved
hypothesis. Known SC'_2 does not by itself yield cubic transfer to arbitrary
first rows: its additional unanchored-cover residual depends on tail-varying
actual linear offsets, while Jensen's fixed-quadratic cost lemma does not.
No such cubic general-row consequence is claimed here.

The square-root scale is what the present selected-matching/Laplace envelope
reaches when k is proportional to q. It is a limitation of that estimate, not
an upper bound for network width. Nor does the fixed-size support union bound
make its n^(1/3) choice intrinsic. The completed Bernoulli-conditioning
transfer gives a stronger verified H-conditional exp(c_C*sqrt(N)) bound for
actual original affine networks with h1<=C*N^2. Its standalone BERNOULLI.md
note states the exact constants, raw-network scope and remaining open H.
This is a stretched-exponential consequence under H.

A true exp(c*n) lower bound would require further structural/counting progress.
Nothing in these results establishes quadratic tightness or rules out such a
bound. All completed results above retain their explicit open H premise.
