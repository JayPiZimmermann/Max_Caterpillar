# Noncrossing Hamiltonian paths do not suffice uniformly

The full noncrossing Hamiltonian-path dictionary is an exponential-size
candidate: there are `n 2^(n-3)` unoriented noncrossing Hamiltonian paths on
`n` cyclically ordered vertices, and five edge states give `poly(N)10^N`
descriptions after apex and head choices. Arbitrary orientations are a
substantial enlargement over the previously tested source/root markings.
Nevertheless the full family fails for every `N>=12`, even with arbitrary
linear heads and signed inner coefficients.

Fix `T={0,2,4,6,8,10}`. These six labels are pairwise separated around the
ambient circle: between any two successive labels of `T` there is at least
one untied label. In particular this remains true between 10 and 0 when
`N>=12`.

Every noncrossing Hamiltonian path admits an endpoint-peeling description.
Start at either endpoint. Its next vertex must be adjacent to it in the
cyclic order of the remaining vertices. Otherwise their edge is a proper
chord with vertices on both sides. After leaving its second endpoint, the
remaining path would have to pass from one side of that chord to the other;
it cannot use either endpoint again, so it would cross the chord. Remove
the first endpoint and repeat. Thus, after the initial vertex, the path
successively visits one of the two ends of the remaining circular interval.

Consider this visit order after one omitted apex `a` is deleted.

- If `a` is outside `T`, its deletion creates at most one adjacent pair of
  tied labels in the circle. During endpoint peeling, a consecutive run of
  tied vertices has length at most two, except for at most one run of
  length three using that unique adjacent pair. The initial run obeys the
  same bound: its next vertex is a circular neighbour of the first vertex.
  Six tied vertices therefore require at least three runs. The induced
  path on `T` has at most `6-3=3` edges.
- If `a` belongs to `T`, the five remaining tied labels are still pairwise
  separated. Every tied run has length at most two, so there are at least
  three runs and at most `5-3=2` induced edges.

Consequently every unit has at most three free comparison directions at
this six-label top tie. Even allowing an arbitrary head gives dependence
on at most four linear forms. The zero-preactivation germ is in `L4`; the
other outer-preactivation cases lie in `L1`. The target germ is `max_6`,
whose simplex has dimension five and is not in `L4`. A finite first-hidden-
layer auxiliary span does not affect this separation.

This proves the stated impossibility. It includes every face state and
arbitrary signed inner weights, because deleting comparisons cannot raise
the free rank and the argument uses linear dependence rather than convexity.
It does not exclude arbitrary noncrossing trees: branching destroys the
endpoint-peeling restriction.

`overnight_upper_path_locality.py` enumerates the complete family using
endpoint peeling. For three through seven vertices it independently checks
that this agrees with all permutations filtered by edge crossings. It then
checks all omitted-apex paths at arities seven through fourteen. The first
alternating-tie obstruction occurs at twelve inputs, with 33,792 graphs
and maximum free rank three. These checks support the elementary uniform
proof above; they are not Lean proofs.
