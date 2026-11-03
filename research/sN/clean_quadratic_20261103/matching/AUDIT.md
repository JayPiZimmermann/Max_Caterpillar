# Independent audit of the elementary matching estimate

Status: the mathematical proof is complete. Its main bound is already a
Lean theorem in the existing matching library. This audit introduces no new
formal theorem and makes no claim of a fresh transitive rebuild.

## Preferred statement and manuscript source

Let G be a simple graph with e edges on m≥2 vertices, let 0≤2J≤m, let M
be a uniformly random J-edge matching, and put X=|M∩E(G)|. Then

    E[θ^X] ≤ exp[-2Je(1−θ³)/(3m(m−1))]       (0<θ≤1).

In particular,

    E[2^(−X)] ≤ exp[-7Je/(12m(m−1))] ≤ exp[-Je/(2m²)].

The complete paper proof is `../probability/matching/lemma.tex`. The longer
explanation and route comparison are in its sibling `argument.md`.
The bound needed for the existential quadratic theorem is the weaker final
display; no optimized matching constant is required.

## Pinning and the conditional law

Generate M using a uniform permutation of m vertices and fixed disjoint
position pairs. For a chosen pair with positions p,q and a fixed oriented
graph edge (a,b), swap a into p and then b into q.

The first forced permutation is uniform conditional on its value a at p:
every such permutation has m preimages, indexed by the original position
of a. The second step acts within that pinned space and has m−1 preimages,
indexed by the position of b after the first swap. That position cannot be p,
because a≠b. Thus every doubly pinned output has m(m−1) preimages. This
includes the cases where a or b was already in its required position.

Forgetting the order and orientations of the pairs gives the uniform
matching conditional on containing {a,b}. Each J-matching containing that
edge has exactly (J−1)! 2^(J−1) (m−2J)! pinned-permutation representations.
Consequently one can pin into the first pair throughout the paper proof;
the formal library's additional random selected-pair index is unnecessary
in this presentation.

## Pointwise change

Only p,q and the two source positions used by the swaps can change. Since
p,q belong to the same selected pair, at most three selected pairs change.
The new count Y therefore satisfies Y≤X+3. This statement is valid without
any independence or degree assumption on G.

## Finite generating-function argument

For each edge ab let X_ab be the coupled count conditional on ab∈M. Its
event probability is p₀=2J/(m(m−1)). If F(t)=E[t^X], then, for 0<t≤1,

    F′(t) = p₀ Σ_ab E[t^(X_ab−1)] ≥ e p₀ t² F(t).

The equality follows simply by expanding X as the sum of graph-edge
indicators. The inequality uses X_ab≤X+3 and the fact that t↦t^r decreases
with r when 0<t≤1. The derivative identity is a finite polynomial identity;
there is no exchange of an infinite sum and derivative. Integrating F′/F
between θ and 1, with F>0 and F(1)=1, proves the assertion.

If J=0 or e=0, X=0 and the result is an equality. No conditional law on an
empty event is used. The optional endpoint θ=0 follows by continuity, but
is not needed by the network proof.

## Formal correspondence

The proof matches these existing declarations exactly:

- `MatchingSizeBias/Forcing.lean`, `forcingEquiv`: the forcing permutation
  and its constant-size fibers. All declarations listed here are in the
  namespace `MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias`.
- `MatchingSizeBias/Damage.lean`, `sampleCoupledCount_le`: the +3 bound.
- `MatchingSizeBias/Identity.lean`, `finite_size_bias_identity`: the finite
  averaging identity.
- `MatchingSizeBias/AllGraphs.lean`,
  `matching_geometric_le_all_graphs` and
  `matching_half_moment_le_all_graphs`: the actual permutation statements,
  with no nonempty-graph assumption. They require J>0; J=0 is immediate.

The later adaptive +2 coupling improves the numerical rate but makes the
conditional-law proof longer. It is a valid refinement for Lean constants,
not the preferred existential-proof presentation. Direct claims of negative
dependence of all graph-edge indicators are false even for m=4,J=2, and
are not used here.

Two independent agents checked the forcing law, count change, derivative
direction, and endpoint cases. Neither found a missing mathematical step.
