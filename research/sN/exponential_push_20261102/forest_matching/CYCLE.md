# Exact graph cycle input for circuit deletion

Status: **Lean verified research leaf**, not integrated into a production
root. Both `cycle_build.exit` and `cycle_check.exit` are zero. The exact-type
and nonvacuity driver is `CycleCheck.lean`; all audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

`Cycle.lean` defines the ordinary simple graph `indexedGraph A a b` of a
finite set of original indices. An edge joins distinct vertices `u,v` when
some index in `A` has endpoints `(u,v)` or `(v,u)`. Parallel indices and loops
in the dictionary are allowed; the simple graph ignores loops.

The theorem `indexedGraph_oriented_cycle` proves that if this graph is not
acyclic, there are a nonempty subset `S ⊆ A` and one Boolean orientation for
each original index such that, **simultaneously for every real input `x`**,
the sum of the oriented forms `x(a i) − x(b i)` over `S` is zero. The more
general `exists_oriented_cycle_of_not_acyclic` only assumes that the edges of
an arbitrary simple graph have representatives in `A`.

The proof takes an actual mathlib graph cycle, selects an original index
for each dart, and uses the cycle's distinct unordered edges to prove that
these selected indices are distinct. Thus global injectivity of the
dictionary is unnecessary. The resulting finite sum is the telescoping sum
of endpoint differences along the closed walk. The separate lemma
`indexedGraph_mono` proves that deleting original indices only deletes graph
edges.

`CycleCheck.lean` checks the exact quantified theorem type and an explicit
three-vertex triangle. Its control dictionary contains all nine ordered
pairs, including loops and both orientations, so the strengthened scope is
exercised without a hidden canonical-index hypothesis.

Reproduce from the repository root:

```sh
mkdir -p .lake/build/lib/research/sN/exponential_push_20261102/forest_matching
python3 research/sN/zulip_three/lean_small_pool.py lake env lean \
  -o .lake/build/lib/research/sN/exponential_push_20261102/forest_matching/Cycle.olean \
  research/sN/exponential_push_20261102/forest_matching/Cycle.lean
python3 research/sN/zulip_three/lean_small_pool.py lake env lean \
  research/sN/exponential_push_20261102/forest_matching/CycleCheck.lean
```

This is the cycle-selection bridge consumed by the original-orientation
three-state circuit deletion. It does not itself prove a matching obstruction
for MAX, a second-hidden-layer width bound, or an exponential lower bound.
