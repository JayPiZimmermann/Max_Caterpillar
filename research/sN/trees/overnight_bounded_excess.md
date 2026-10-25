# Matching witnesses with edges beyond a pseudoforest

25 October 2026. This is a uniform mathematical extension of
`overnight_pseudoforest_matching.md`, not a Lean theorem. It concerns exact
representations of `max_N` by two-hidden-layer units with arbitrary real
linear heads, coefficients, output signs and biases, and a shallow remainder.
Each unit's first hidden layer uses coordinate differences along a simple
comparison graph. Opposite orientations can be absorbed into the head.

For a graph G, write nu(G) for its maximum matching size, z(G) for its
number of isolated vertices, and

    b(G) = sum over connected components C of max(0, |E(C)|-|V(C)|).

Thus b counts the edges that remain after retaining a spanning pseudoforest,
with one cycle in every originally cyclic component. In particular b=0 for
every pseudoforest, even if it has many cyclic components.

Suppose every second-hidden-layer comparison graph satisfies
`nu(G)+z(G)>=k` and `b(G)<=b`. Then the number K of units, and also the number
of distinct comparison graphs, obeys

    K >= [1-(1+N+binom(N,2))*2^(-N)] / Pr[Bin(k,1/4)<=b+2].

The binomial probability is interpreted as 1 when b+2>=k. Explicitly it is

    4^(-k) sum_(j=0)^min(k,b+2) binom(k,j) 3^(k-j).

If k is at least a fixed positive multiple of N and b=o(N), this gives

    K >= exp[(log(4/3)-o(1))*k].

More generally, k=Omega(N) and limsup b/k<1/4 suffice for an exponential
lower bound. This has no maximum-degree restriction.

## Proof

Start with a maximum matching M in G. Since M is acyclic, extend it to a
spanning forest. In every originally cyclic component add any one omitted
edge. The resulting spanning pseudoforest P contains M, has exactly the
same isolated vertices as G, and omits exactly b(G) edges.

Orient P with indegree at most one. For each matched edge, the event that
its child belongs to a random vertex subset T and its parent does not has
probability 1/4. It forces a distinct component of P[T]. An originally
isolated vertex belongs to T with probability 1/2 and gives another distinct
component. These events are mutually independent because their vertex sets
are disjoint. Their count W therefore stochastically dominates Bin(k,1/4).

Restoring any omitted edge can merge at most two induced components, so

    c(G[T]) >= c(P[T])-b(G) >= W-b(G).

The germ locality argument for arbitrary heads implies that a unit can
contribute to a tied set T of size at least three only if c(G[T])<=2.
Its probability of covering such a set is therefore at most
Pr[Bin(k,1/4)<=b+2]. Every such T needs a covering unit. A union bound gives
the claimed inequality; the same argument groups all units with the same
comparison graph into one coverage event.

For the asymptotic assertion, put t=(b+2)/k. When t<1/4, the usual exponential
Markov argument for a binomial variable gives

    Pr[Bin(k,1/4)<=tk] <= exp[-k D(t || 1/4)],

where D(t||q)=t log(t/q)+(1-t)log((1-t)/(1-q)). This follows directly by
optimizing exp(-lambda*t*k)*(3/4+exp(lambda)/4)^k over lambda<0.
As t tends to zero, D(t||1/4) tends to log(4/3).

## Mixtures containing the original constructions

The same extension can be added to the caterpillar and rooted-star face
dictionaries. Suppose the added arbitrary-weight comparison graphs have
matching size at least k, where 2k<=N, and excess at most b. Put

    P_N = 1 + 2N/11 + (4/121) binom(N,2),
    D_(k,b) = sum_(j=0)^min(k,b+2) binom(k,j) (22/147)^j.

Then the total number Z of dictionary functions in an expansion satisfies

    Z >= (169/147)^k / [P_N + N - 2 + D_(k,b)].

To see this, select vertices with probability p=2/13, so each matching
witness has probability 22/169. The preceding argument bounds the new
unit's weighted coverage by E*D_(k,b), where
E=(13/11)^N*(147/169)^k. The original dictionary has coverage at most
(N-2)*(12/11)^N, and E>=(12/11)^N>=1. The total target weight is
(13/11)^N-P_N. Since Z>=1, move P_N to the right and use the same union
bound to obtain the displayed inequality. For b=0 the denominator is at
most (N+1)^2, recovering the earlier mixture theorem.

If k=Omega(N) and b=o(N), then log D_(k,b)=o(N), so this is still an
exponential bound, with rate k*log(169/147)-o(N). Thus the extension also
applies to a spanning dictionary that includes both original combinatorial
constructions; it is not merely a conditional bound for an unproved new
dictionary.

## Controls and scope

`overnight_bounded_excess_check.py` exhausts every simple labelled graph on
at most six vertices, constructs the matching-preserving pseudoforest, and
checks every selected vertex subset and the exact probability bound. These
are independent finite controls of the uniform proof, not a replacement for
it. The result does not prove the unrestricted canonical all-tree exponential
bound: trees with sublinear matching and few isolated vertices remain outside
its exponential regime.
