# A stronger weighted bounded-degree bound by iterated Holder

25 October 2026. Uniform mathematical proof, not Lean verified. The model is
the arbitrary-head and arbitrary-weight comparison-graph model of
`overnight_bounded_excess.md`, including biases and a shallow remainder.

Suppose every comparison graph has maximum degree at most Delta>=1. Put

    r=Delta+1, p=1/r, q=p(1-p)^Delta,
    tau=Pr[Bin(N,p)>=3], eta=2/N.

If eta<q, every exact expansion of max_N uses at least

    |K| >= tau * exp[(N/r) D(eta || q)],

where D(t||q)=t log(t/q)+(1-t)log((1-t)/(1-q)). The same lower bound counts
distinct comparison graphs. For each fixed Delta this gives

    |K| = Omega_Delta((1-q)^(-N/(Delta+1)) / N^(2/(Delta+1))).

It improves the earlier square-neighborhood coloring bound for general
bounded-degree graphs. The matching proof remains stronger in the
pseudoforest regime.

## The elementary product inequality

Let X_1,...,X_m be independent, and let nonnegative functions f_v depend on
these inputs so that each input appears in at most r functions. Then

    E product_v f_v <= product_v (E f_v^r)^(1/r).

An induction on the number of inputs proves this directly. Condition on
all but one input and apply r-fold Holder to its incident factors, padding
with constant ones if necessary. Replace each such factor by
(E_input f_v^r)^(1/r). The remaining functions still have the same dependency
bound. Apply induction; taking the r-th power of the replaced factors
restores E_input f_v^r, yielding the stated inequality.

This is the relevant special case of Finner's generalized Holder inequality.
The corresponding concentration theorem for functions with limited input
dependence is given by Gavinsky, Lovett, Saks and Srinivasan,
[A Tail Bound for Read-k Families of Functions](https://arxiv.org/abs/1205.1478),
Random Structures & Algorithms 47 (2015), 99-108,
[doi:10.1002/rsa.20532](https://doi.org/10.1002/rsa.20532).
The proof here includes the needed special case rather than assuming that
the overlapping neighborhood events are independent.

## Application to graph coverage

Select each vertex independently with probability p. Let Z_v indicate that
v is selected and all its neighbors are absent. Each underlying vertex bit
occurs in at most Delta+1 of these indicators. Moreover

    Pr[Z_v=1]=p(1-p)^deg(v) >= q.

Write Z=sum_v Z_v. For t>=0, apply the product inequality to f_v=exp(-t Z_v):

    E exp(-t Z) <= (1-q+q exp(-rt))^(N/r).

Every selected isolated vertex gives its own induced component. Thus the
event c(G[T])<=2 requires Z<=2. Exponential Markov and the substitution
u=rt give

    Pr[c(G[T])<=2]
      <= inf_(u>=0) [exp(2u)(1-q+q exp(-u))^N]^(1/r)
      = exp[-(N/r) D(2/N || q)]                 when 2/N<q.

Every tied set of size at least three needs a graph with at most two
induced components, by the existing germ-rank argument. Their probability
is tau, so the union bound proves the result. Different heads or weights
on the same graph do not add new coverage events.

Finally,

    N D(2/N || q)
      = -N log(1-q) - 2 log N
        + 2 log(2(1-q)/q) - 2 + O(1/N),

which gives the asserted asymptotic estimate. The choice p=1/(Delta+1)
maximizes p(1-p)^Delta.

## Exact controls

`overnight_read_degree_check.py` evaluates the moment inequality using only
integers on every simple graph through six vertices and every vertex subset.
It checks both the individual marginal product and its common-q bound.
Disjoint-clique controls at larger N also check the optimized lower-tail
bound against an exact binomial coverage probability. These finite controls
support the uniform proof; they do not prove an unrestricted all-tree bound.
