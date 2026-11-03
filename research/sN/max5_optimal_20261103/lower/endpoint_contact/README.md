# Endpoint derivative constraints for two shallow cores

Status: two exact Lean declarations and their axiom closure pass the
bounded replay in `receipt.json`. This is a necessary condition for the
specified exact representation; it is not a completed width lower bound
or a classification of all Max5 networks.

Suppose MAX5=R+ReLU(g)+ReLU(h) on every real input. The remainder R is an
arbitrary affine-plus-shallow-ReLU function. At q_i=-e_i, suppose both
cores are zero. For every j distinct from i, at least one of the two
one-sided directional slopes in direction -e_j is zero.

For a homogeneous first layer and optional affine head,

```
g(x) = head dot x + constant + sum_k c_k ReLU(A_k dot x),
```

the explicitly verified slope is

```
D_g(i,j) = -head_j + sum_k c_k *
  (if A_ki < 0 then -A_kj
   else if A_ki = 0 then ReLU(-A_kj)
   else 0).
```

The theorem is D_g(i,j)=0 or D_h(i,j)=0. It keeps signed coefficients,
zero entries, repeated rows, cancellations, arbitrary widths, and distinct
feature spans for g and h. The shared-zero assumptions are explicit.

The more general declaration also retains arbitrary first biases β_k.
It evaluates the branch on the preactivation β_k-A_ki and applies it to
the directional increment -A_kj. No bias-removal argument is needed.

The proof first establishes an exact finite-sum ray identity
f(q+εv)=f(q)+εD for all sufficiently small ε>0. The frozen weighted
triple-contact theorem forces one core to vanish at q_i-εe_j. The two
shared zeros reduce this to εD_g=0 or εD_h=0; ε>0 permits cancellation.
There is no limit interchange, genericity assumption, or nonzero-entry
cutoff.

`EndpointContact.lean` contains the general
`shared_endpoint_directional_disjunction` and the explicit homogeneous-row
`shared_endpoint_slope_disjunction`. `Statements.lean` checks their exact
expected types. Its second consumer unfolds the slope to the literal
piecewise expression with `max 0`, so the branch convention used by
arithmetic models is checked directly.

Both declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
Run the reproducible targeted check from the repository root:

```
python3 research/sN/max5_optimal_20261103/lower/endpoint_contact/verify.py --replay
```

The verifier builds the existing dependency target, re-elaborates the
frozen triple-contact module, compiles this new module and its exact-type
consumer, scans the local source closure for prohibited proof constructs,
and records hashes. It does not mutate the frozen triple-contact sources
or receipts. This artifact has not been added to the repository-wide
public theorem manifest or aggregator.
