# Actual finite-network cycle elimination

This development completes the model bridge for the circuit identity in
`../../exponential_push_20261102/structural/CircuitDeletion.lean`. Its target
is an exact same-arity equivalence of two representable function classes.
It does not prove a new MAX obstruction by itself.

For a normalized homogeneous braid network, define its interaction graph
using the actual signed sum of all parallel first-hidden rows. The graph
therefore includes cancellations, rather than taking a union of supports.
For every nonnegative integer r and every real function f on N inputs:

* f has a finite such network whose every second-hidden interaction graph
  has matching number at most r if and only if
* f has a finite such network whose every second-hidden interaction graph
  has a vertex cover of size at most r.

All real weights, linear heads, and braid first-hidden output skips are
allowed. Both representations have the same input arity and the same
function on every real input. Hidden widths can differ. Because normalized
networks have diagonal translation slope one, these are representability
classes, not unqualified vector spaces under scalar multiplication.

The corresponding structural theorem is
`localMatchingObstruction_iff_no_cover_representation`: H(N,r+1), the
existing actual-network matching obstruction, is equivalent to excluding
cover-r networks for MAX_N. This improves the elementary matching-to-cover
comparison without asserting that either obstruction has been proved for
new r. In particular, an actual cover-(q-1) obstruction at 2q+1 inputs would
give H(2q+1,q).

## Proof and model accounting

The earlier exact circuit identity deletes at least one edge of a cycle in
every term of a finite signed expansion. Reorienting a retained edge moves
a linear term into the head. Each original oriented edge has three possible
states: omitted, linear, or nonlinear. Induction on active edge count leaves
only forest graphs. One finite coefficient function is chosen for all real
inputs simultaneously.

`NetworkExpansion.lean` constructs an ordinary `NormalizedNetwork` from
those families using the verified finite-index constructor. Its first layer
contains one oriented root for each unordered input pair. Its second layer
is indexed by the pairs (original second-hidden index, forest state), then
reindexed as a `Fin` array. All linear corrections enter the corresponding
zero-sum head. The original shallow output is canonically regrouped with its
linear correction, whose total coordinate sum remains one.

`StateGraph.lean` proves from the literal signed edge-weight formula that
each new actual interaction graph is contained in its forest-state graph.
`ExpandedGraphs.lean` then proves acyclicity and containment in the graph of
one original neuron. A no-(r+1)-matching premise on that original graph gives
an actual cover of size at most r for the new neuron, by the previously
verified forest matching/cover theorem.

The reverse implication uses `MatchingCover.lean`: an ordinary disjoint-edge
matching cannot have more edges than an endpoint vertex cover. It requires
no forest assumption and no new construction.

The actual constructed second hidden width is at most

    original h2 * 3^(number of unordered input pairs).

This deliberately coarse bound demonstrates finite size; it is not a useful
width-preserving transfer of lower bounds. The proof contains no coefficient
norm estimate, nonnegativity assumption, rationality assumption, or
generic-position exception.

## Verification

The exact declarations, raw finite-network contract, nonempty cyclic input
control, and small-arity control are checked by `Check.lean` and
`MatchingCoverCheck.lean`. The source closure, logs, and accepted axioms are
recorded in `receipt.json` after a successful run of:

```sh
python3 research/sN/overnight_20261103/cycle_bridge/recheck.py --run
```

These are isolated research declarations. They have not been imported into
the frozen production facade. The receipt records their precise verified
state; a proposed target or a partial build is not a completed gate.
