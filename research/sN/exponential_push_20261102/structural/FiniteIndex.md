# Finite-index constructor for the actual forest-network lift

`FiniteIndex.lean` supplies `MaxCaterpillar.ExponentialPush.FiniteIndex.indexedNetwork`. It takes arbitrary finite types J,K and arrays

    A:J→Point N, U:K→Point N, W:K→J→R,
    L:Point N, B:J→R, d:K→R

and constructs the actual `NormalizedNetwork N (card J) (card K)` using `Fintype.equivFin`. There are no nonempty, decidable-equality, or positive-width assumptions. The constructor does not normalize, merge, or discard any supplied term.

The verified identities are:

* `sum_equivFin_symm`: ordinary real finite sums are unchanged.
* `inner_indexed`: at outer index `Fintype.equivFin K k`, the actual inner value is exactly `lin(U k,x)+sum_j W k j*relu(lin(A j,x))`.
* `eval_indexed`: the complete actual evaluation equals the supplied finite-family expression, including L/B output skips.
* `rowSupport_indexed`: the actual support at `Fintype.equivFin J j` is exactly the support of A j.
* `rowSupport_card_le_indexed`: the all-row cardinality bound is equivalent before and after reindexing.
* `translationNormalized_indexed`: actual normalization is equivalent to zero coordinate sums for every supplied A/U row and unit sum for L.
* `braidEdgeWeight_indexed`: the actual signed interaction sum equals

      -sum_j, if support(A j)={a,b} then W k j*|A j a| else 0.

The last identity retains arbitrary signed cancellations among parallel rows. No positive-coefficient assumption is introduced.

`FiniteIndexCheck.lean` independently consumes the expanded inner, evaluation, and interaction types. It also constructs a genuine one-input normalized network with BOTH index families empty and checks its evaluation equals the input. This validates the zero-width boundary rather than hiding an index inhabitance assumption.

The canonical research artifact is `.lake/build/lib/research/sN/exponential_push_20261102/structural/FiniteIndex.olean`. Reproduce its build under the shared pool:

    python3 research/sN/zulip_three/lean_small_pool.py lake env lean -j1 \
      research/sN/exponential_push_20261102/structural/FiniteIndex.lean \
      -o .lake/build/lib/research/sN/exponential_push_20261102/structural/FiniteIndex.olean
    python3 research/sN/zulip_three/lean_small_pool.py lake env lean -j1 \
      research/sN/exponential_push_20261102/structural/FiniteIndexCheck.lean

This is an isolated research leaf for component65_audit's actual forest expansion. It does not prove H(13,3), a new width lower bound, or a new analytic obstruction. Its receipt is separate from the frozen `structural/receipt.json`.
