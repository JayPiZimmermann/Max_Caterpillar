# Coordinate-deletion closure of canonical cycle states

The top-dimensional five-state cycle family consists of:

- a full cycle on all nonapex vertices, arbitrary hinge orientations, and
  head `x_root-x_apex`;
- a Hamiltonian path on those vertices, arbitrary hinge orientations, and
  head `x_root-x_apex+s(x_u-x_v)`, where `u,v` are its endpoints and
  `s` is `-1`, `0`, or `1`.

The second case is precisely one cycle edge replaced by a linear state or
omitted. With at least two nonhinge edges, the pyramid already belongs to
`L_(N-2)` and an opposite-face difference lies in `L_(N-3)`. Thus these
other states do not affect propagation in the lower top quotient.

Deleting the apex gives only a zonotope support function, in `L1`.
Deleting an internal path vertex freezes two hinges, leaving at most
`N-4` generators and hence pyramid dimension at most `N-3`. Both vanish
in the lower-arity top quotient.

For a path endpoint `u`, write `j` for its neighbour and `v` for the other
endpoint. Put `p=1[root=u]`. Use shift convention `s(x_u-x_v)`, and let
`tau=1` for the incident hinge `sigma(x_u-x_j)` and `tau=-1` for its reverse.
The outer preactivations at `+e_u` and `-e_u` are respectively

```
A_plus  = p+s + 1[tau=1],
A_minus = -(p+s) + 1[tau=-1].
```

Only a zero preactivation gives a nonlinear pyramid germ. The cases are:

| Direction | Conditions | Surviving head on the shortened path |
|---|---|---|
| `+e_u` | `tau=1,p=0,s=-1` | `x_root-x_apex-(x_j-x_v)` |
| `-e_u` | `tau=-1,p=0,s=1` | `x_root-x_apex+(x_j-x_v)` |
| `-e_u` if `tau=1`, otherwise `+e_u` | `p=0,s=0` | `x_root-x_apex` |
| `-e_u` if `tau=1`, otherwise `+e_u` | `p=1,s=-1` | `x_v-x_apex` |
| `-e_u` | `tau=-1,p=1,s=0` | `x_j-x_apex` |

This list is exhaustive since `p` is zero or one and `s` belongs to
`{-1,0,1}`. The free graph is the shortened path with endpoints `j,v`,
so every surviving head has the required form.

For a full cycle, let `k` count the incident hinges whose positive endpoint
is the deleted vertex, and again put `p=1[root=deleted]`. The two outer
values are `p+k` and `-p+2-k`. Zero occurs only at a nonroot sink, a
nonroot source, or a root with one hinge of each orientation. The first
two keep the canonical head; the third moves the root to the neighbour
whose incident hinge is active. Every surviving graph is a path, and its
head is canonical (endpoint shift zero).

Consequently coordinate deletion sends the full cycle-state span into the
same family at one lower arity, modulo the lower dimension filtration.
Since the appropriate opposite-face difference sends `max_N` to
`max_(N-1)` up to a linear function, an exact obstruction at arity seven
propagates to all arities at least seven. This is a conditional consequence
until that finite obstruction has independently passed its exact gate.

`overnight_upper_cycle_delete.py` independently enumerates raw heads, every
root/orientation/endpoint-shift choice, every deleted label, and both
directions for arities four through nine. It checks every surviving head
against the lower path-state family without using the Fourier evaluator.
These are exact research controls, not Lean proofs.
