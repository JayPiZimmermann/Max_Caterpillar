# Matching witnesses give shorter and broader weighted-forest bounds

25 October 2026. This is a uniform mathematical proof, independently reviewed
by the construction agent. It is not a Lean theorem. It strengthens the
bounded-degree forest bound and extends the large-matching mixture bound to
arbitrary real heads and inner coefficients. The unrestricted all-tree
exponential bound remains open.

## Model and locality

Consider an exact representation

`max_N = R + sum_j d_j sigma(h_j(x) + sum_(uv in G_j) c_juv sigma(x_u-x_v))`.

Here `R` is an arbitrary shallow ReLU function, each `h_j` is an arbitrary
linear form, and all coefficients are arbitrary real numbers. Every `G_j`
is a simple forest on the `N` input labels, including isolated vertices.
Zero coefficients may be omitted or retained in the specified forest.
Biases are allowed by taking recession functions.

At a generic top tie on a set `T` of `m>=3` labels, frozen comparisons
are locally linear. The free comparisons span a space of dimension at
most `m-c(G_j[T])`, where isolated tied labels count as components. One
linear head adds at most one dimension. Thus if `c(G_j[T])>=3`, the local
unit lies in `L_(m-2)`. The maximum has nonzero simplex class there, and
the shallow remainder vanishes in this quotient. Every such tie must
therefore have `c(G_j[T])<=2` for some contributing graph. This is the
locality lemma in `overnight_degree_two.md`.

## Independent component witnesses

Root each component of a forest `G`, and choose a matching of size `k`.
Select each vertex independently with probability `p`. For a matched
parent-child edge, the event

`parent not selected, child selected`

has probability `r=p(1-p)`. Each such child is the highest vertex of a
different component of `G[T]`. The events are independent because the
matching edges have disjoint endpoints. Consequently, with `rho=1-r`,

`Pr(c(G[T])<=2) <= rho^k [1+k r/rho+binom(k,2)(r/rho)^2]`.       (1)

This does not require a degree bound, an orientation restriction, a
canonical head, or positive inner coefficients.

Let `nu(G)` be the maximum matching size and let `z(G)` be the number of
isolated vertices. Each selected isolated vertex gives another independent
component witness, on labels disjoint from the matching endpoints. At
`p=1/2` its probability is `1/2`, whereas a matching witness has probability
`1/4`. Replacing the former by probability `1/4` can only increase the
probability of at most two witnesses. Thus, if `nu(G)+z(G)>=k`,

`Pr(c(G[T])<=2) <= (3/4)^k C_k`,
`C_k = 1+k/3+binom(k,2)/9`.                                  (2)

The binomial lower tail decreases with the number of trials, so the same
bound applies when the forest supplies more than `k` witnesses.

## Uniform lower bound

Put `B_N=1+N+binom(N,2)`. If every comparison forest satisfies
`nu(G_j)+z(G_j)>=k`, then for `N>=3`,

`|K| >= (1-B_N/2^N) (4/3)^k / C_k`.                           (3)

Indeed, under uniform subset selection the probability of `|T|>=3` is
`1-B_N/2^N`. Cover these ties by the graph events in (2) and apply the
union bound. The same argument counts distinct comparison graphs rather
than neurons, since the necessary component condition depends only on
the graph.

In particular, (3) holds if every forest has matching number at least
`k`. A matching of linear size gives an exponential lower bound for all
real heads and weights, even with unbounded vertex degrees.

## Bounded degree as an immediate corollary

A forest has a vertex cover of size `nu(G)`. An elementary proof repeatedly
chooses a leaf and its neighbor: a maximum matching can be chosen to use
that leaf edge, and deleting both endpoints reduces its size by one;
choosing the neighbor for the cover and recursing covers every edge.

If the maximum degree is `Delta`, every nonisolated vertex outside this
cover has a neighbor in it. Therefore

`N-z(G)-nu(G) <= Delta nu(G)`,
`nu(G)+z(G) >= ceil(N/(Delta+1))`.

Use this last integer as `k` in (3). The result is

`|K| = Omega_Delta((4/3)^(N/(Delta+1))/N^2)`.

This improves the base `27/23` in `overnight_bounded_degree.md` and replaces
its square-coloring and arithmetic-geometric-mean proof for forests. The
older general bounded-degree graph argument remains valid: matching
witnesses need not create different components when cycles are present.
The sharper degree-two path/cycle bound also remains preferable in that
special case.

## Mixtures containing the original constructions

Let the base class be the caterpillar and rooted-star face functions from
the paper. Its weighted locality count is at most `6^m` for ties of size
`m`, after dividing the permutation count by `m!(N-m)!`. Add arbitrary
weighted-forest units as above whose specified forests have matching
number at least `k`, where `0<=2k<=N`. An auxiliary remainder is allowed.
Then the total number of counted terms satisfies

`Z >= (169/147)^k/(N+1)^2`.                                  (4)

Thus this genuinely larger dictionary includes the building blocks of
both combinatorial constructions, while the added units may have arbitrary
heads and real weights.

For completeness, set `y=2/11`, `p=y/(1+y)=2/13`, `rho=147/169`, and

`D_k=1+(22/147)k+(22/147)^2 binom(k,2)`,
`E=(13/11)^N rho^k`.

Equation (1), summed with subset weights `y^|T|`, bounds each added unit's
contribution by `E D_k`. The base contribution is at most
`(N-2)(12/11)^N`. Since `2k<=N` and `147>=144`,
`E>=(12/11)^N>=1`. Write `P=1+Ny+binom(N,2)y^2`. Coverage and `Z>=1` give

`(13/11)^N <= [P+(N-2)+D_k] E Z`.

Using `y<=1/2`, `22/147<=1`, and `k<=N/2`, the bracket is at most
`2N+N^2/4 <= (N+1)^2`. Cancel `(13/11)^N` to obtain (4).

The same argument permits a free class of canonical tree-face functions
annihilated by a separator at every tie size `m>=s`. For arbitrary oriented
canonical stars use `s=5`; the bound is `(169/147)^k/(N+1)^4` on the other
terms. For original canonical trees of matching number at most two, the
exact seven-label separator in `overnight_lower.md` gives `s=7` and
denominator `(N+1)^6`. These free classes retain their canonical heads and
unit edge coefficients; they are not arbitrary weighted stars or trees.
The proof merely starts the same weighted coverage sum at `s` and absorbs
the omitted terms of degrees at most `s-1` into that polynomial factor.

Neither the matching hypothesis nor the degree corollary covers all trees
uniformly: trees with a growing but sublinear matching number and large
degree remain outside the exponential regime of this argument.
