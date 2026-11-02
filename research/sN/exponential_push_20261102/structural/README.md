# Exact structural reduction: matching obstructions are cover obstructions

**Result:** cyclic comparison graphs add no functions to the finite signed span beyond weighted forest-subgraph neurons. In particular, at the same input arity, H(k,q) is equivalent to the vertex-cover-(q-1) obstruction. This is an exact all-real pointwise reduction, not a survivor-only argument or a finite-dictionary observation. The remaining weighted two-cover forest obstruction, including H(13,3), is unresolved here.

The scalar identity below is Lean verified in the isolated `CircuitDeletion.lean`, with only `propext`, `Quot.sound`, and `Classical.choice`. The full finite-graph/network consequence is proved mathematically below; its formal model bridge is a separate task owned by component65_audit. No published Lean source is modified.

## 1. Circuit deletion

Let C be a nonempty finite index set, let ell_i be real linear forms satisfying sum_C ell_i=0, and let c_i be arbitrary real coefficients. For every x at least one ell_j(x)<=0, hence sigma(ell_j(x))=0. Thus, for any baseline A(x) and ANY scalar outer function F,

    F(A + sum_C c_i sigma(ell_i))
      = sum_{nonempty J subset C} (-1)^(|J|+1)
          F(A + sum_{i in C\J} c_i sigma(ell_i)).

To prove it, include J=empty and consider the full alternating sum. Pair each omission set J with J symmetric-difference {j}. The two arguments agree because the j-th hinge is zero, and their signs are opposite. The full sum is zero; move the empty-set term to the other side. Boundary cases with multiple zero hinges work identically. No sign condition on c_i and no regularity, homogeneity, or convexity of F is used.

`MaxCaterpillar.ExponentialPush.circuit_deletion` states the equivalent proper-KEPT-subset formula, avoiding any reindexing convention in the checker. The proof uses finite anchored inclusion-exclusion from the already verified `StarCertificate.Anova` module.

## 2. Apply to graph cycles

A braid preactivation has form

    g(x)=h(x)+sum_{e in E} c_e sigma(ell_e(x)),

where E is a finite simple comparison graph, ell_e is one orientation of x_a-x_b, and h is an arbitrary real linear form. Zero coefficients can be discarded, and parallel/opposite comparisons can be aggregated using sigma(-t)=sigma(t)-t.

Take any simple cycle v_1,...,v_m,v_1. Orient its comparisons cyclically, ell_i'=x_(v_i)-x_(v_(i+1)), so their sum is zero. If an original comparison has the opposite orientation, use

    c_i sigma(-ell_i')=c_i sigma(ell_i')-c_i ell_i'

to put its linear correction into h. The coefficients remain arbitrary real numbers. Apply circuit deletion with baseline h plus all noncycle hinges. Every resulting term omits at least one edge of this cycle; all other edges are unchanged. Therefore the total number of nonlinear comparison edges strictly decreases.

Strong induction on |E| gives a finite signed expansion into forest-subgraph neurons, with shifted real heads. It is a global pointwise identity, so replacing all neurons in an actually glued network preserves the network function and all crease cancellations automatically. Finite width may increase; the local structural impossibility question quantifies over every finite width, so this causes no logical loss.

Every retained graph is an edge-subgraph of the original graph. Hence its matching number cannot increase. If the original head has coordinate sum zero, every shifted head still does, since every root difference does. Translation normalization is preserved. There is no fixed finite rational/canonical dictionary claim: the edge lengths and heads retain the original real data.

One cycle of length m produces at most 2^m-1 terms. A triangle is exactly three two-edge terms minus three one-edge terms plus one modular term, after the orientation correction. This gives an immediate actual-network proof of triangle redundancy from the arbitrary-head star obstruction. It does not assume that the nonlinear Xi parameter expression is linear under arbitrary unit identities.

## 3. Matching versus cover, at identical arity

Write V_match(r) for the finite signed span of normalized neurons whose interaction graph has matching number at most r, and V_cover(r) for the corresponding vertex-cover class.

* V_cover(r) is contained in V_match(r), because any matching has at most one edge for each vertex of a cover.
* Cycle deletion expresses every generator of V_match(r) as forest-subgraph generators with matching number at most r.
* For a finite forest, minimum vertex-cover size equals maximum matching size. This follows either from bipartite Konig or directly by leaf induction: choose leaf v with neighbour u; some maximum matching contains uv by an exchange; delete u,v; add u to a minimum cover of the remaining forest.

Therefore V_match(r)=V_cover(r). The equality holds for actual functions before imposing gluing, with arbitrary real weights and heads. Consequently H(k,q), which forbids MAX_k using matching number at most q-1, is equivalent to the K_(q-1) obstruction at the SAME k. The same conclusion applies to a top-Mobius gluing obstruction if that is the formulation proved for K_(q-1).

This supersedes the earlier concern that apex-plus-triangle and K5/small-core interaction graphs require independent matching-two obstructions. As graphs they do lie outside cover two; as neurons they expand into cover-two forests with modified heads. Tutte–Berge classification is no longer needed for this reduction.

Conditional bookkeeping improves too: SC'_q includes K_(q-1), so it implies H(2q+3,q). The elementary maximal-matching-cover argument only gave SC'_(2q-1) => H(4q+1,q). This improves which structural hypotheses the random-matching transfer would need. It is not a proof of SC'_q or of an exponential network bound.

## 4. Exact remaining matching-two shapes

For a forest with cover {a,b}, every noncenter vertex is a leaf attached to a or b, except possibly one common middle vertex adjacent to both. There cannot be two common middle vertices, since those create a four-cycle. If a,b are adjacent, there is no such middle vertex, since that creates a triangle. Thus, allowing missing leaves/edges/components, the nonlinear forest is one of:

* a double-star with adjacent centres;
* a subdivided double-star, whose centres have distance two;
* two disjoint stars.

A single star and isolated labels are included as degeneracies. Linear coefficients on isolated labels remain arbitrary and cannot be silently deleted. The real head is arbitrary on ALL labels; it does not have to be a root difference or satisfy an anchor condition.

The residual is now precise: prove that a finite signed, actually glued network of these arbitrary-head, arbitrarily weighted forests cannot compute MAX_13 (or MAX_k at any fixed finite modest k). Known SC'_2 does not give this, because it treats anchor-two neurons and stars rather than every arbitrary-head two-cover forest. The exact linear decomposition G=H_anchor2+M_modular is not a ReLU decomposition.

The child `two_hub_reduction` separately proves negative-hinge elimination and a commensurable-length splitting identity. These reduce the geometric picture to positive weighted forest zonotopes and, for rationally commensurable lengths, to equal lengths with shifted arbitrary heads. They do not make the available canonical-tree separators applicable to all real heads. A density argument would also need to preserve exact gluing, which parameter approximation alone does not do.

## Evidence and scope

* `CircuitDeletion.lean`: four generic finite/all-real theorems, kernel PASS, standard three axioms.
* `CircuitDeletionCheck.lean`: independent expanded contract and arbitrary-real cyclic three-difference instantiation.
* `small_core_quotient/README.md` and its exact producer: independent mathematical audit and 104,625 exact rational controls for cycles of lengths 3,4,5, including zero weights and boundary points and arbitrary nonlinear/discontinuous outer functions.
* `component65_audit` owns further research-only original-orientation, three-state, and graph/model expansion proofs. Do not infer those from this scalar artifact until their own checks pass.

The initial Cayley-subdivision proposal is superseded by the elementary identity. No polyhedral subdivision or support-valuation lemma is needed for the cycle result.

## 5. Arbitrary-arity actual-network bridge

The research module `ActualBraid.lean` now derives a canonical pair-coefficient presentation directly from an actual `NormalizedNetwork N h1 h2` whose original zero-sum first rows have support at most two. It works for every N, including the zero-row N=0/1 cases, and retains all original second-layer indices and all output-only skips.

For p=(a,b), a<b, put

    c_p = sum_{j: support(A_j)={a,b}} W_j |A_j(a)|
        = -braidEdgeWeight(A,W,a,b),
    H = U + (1/2) sum_j W_j A_j - (1/2) sum_p c_p (e_a-e_b).

Using sigma(t)=(t+|t|)/2 gives the all-input identity

    lin(U,x)+sum_j W_j sigma(lin(A_j,x))
       = lin(H,x)+sum_p c_p sigma(x_a-x_b).

The proof derives the two-point support representation; it does not assume a braid row-pair characterization. Zero rows require no dummy pair, and signed parallel-row cancellations are explicitly preserved. `head_sum` proves sum H=sum U, so inner heads retain zero translation slope and the output head retains slope one. The same construction applies to the output-only B coefficients.

`ActualBraidGraph.active_indexedGraph_eq` proves that the finite expansion graph, indexed only by c_p!=0, is exactly the original normalized model's `braidInteractionGraph`. Thus a cancellation to zero cannot leave a spurious active edge. `ActualBraidCheck.lean` independently checks expanded inner/output contracts, actual opposite-row cancellation, and a nonvacuous N=1 model with nonzero feeding/output skips.

This removes the earlier Fin5-only row-pair adapter from the prospective H↔cover bridge. It is still separate from the unresolved analytic obstruction for weighted cover-two forests.
