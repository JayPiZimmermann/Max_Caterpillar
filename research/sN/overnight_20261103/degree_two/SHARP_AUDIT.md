# Independent audit of the sharp degree-two bound

The sharp result was reviewed separately from the frozen audit in `AUDIT.md`.
No mathematical gap was found in the new graph count, width assembly, or
arithmetic constant. The raw-network hypotheses retain their previous scope.

The exact conclusion is

    2 choose(N,m) <= h2 [2N+(m-1)N^2],  m >= 3,

and consequently, for N >= 6,

    h2 >= 4 * 2^N / [N^3(N+1)].

## Additional steps inspected

* Every connected k-subset with k >= 2 supplies the first directed edge of
  a spanning simple path and the first directed edge of its reversal. These
  darts are distinct because a nontrivial simple path has distinct endpoints.
  This remains true when the induced subset is an entire cycle: the spanning
  path omits a cycle edge and still has distinct endpoints.
* A fixed dart and fixed path length determine at most one support in a
  graph of maximum degree two. Counting the two distinct preimages therefore
  gives twice the connected-subset cardinality at most the number of darts.
  The sum of graph degrees is at most 2N. Singleton sets give the same
  connected-subset bound N separately.
* The connected/two-component decomposition retains the earlier factor two
  for ordering distinct nonempty components. The resulting integer bound is
  2 times the two-component subset count at most 2N+(m-1)N^2. No division or
  natural-number truncation loses a factor.
* At m=floor(N/2), twice the sharp capacity is at most N^3 for N >= 2.
  Multiplying the exact width count by two and then using the central
  binomial estimate gives the factor four in the power bound. Positivity of
  the real denominator is proved before division.

## Feeding-only normalized generalization

`FeedingComponents.lean` masks first rows separately for the one original
second neuron being analyzed. The mask removes only rows whose coefficient
into that neuron is zero. It preserves that neuron's entire preactivation
and its signed interaction graph exactly. The proof never asserts that the
masked *whole network* computes MAX. Output-only first neurons are handled
separately as shallow terms by the finite-difference obstruction.

`ActualTieFeeding.lean` proves that a nonzero localized coefficient came from
the same nonzero original coefficient. Its support hypothesis is therefore
applied to original feeding rows only. The actual signed graph comap is
unchanged. The normalized feeding theorem still explicitly requires
translation normalization, including zero coordinate sums for all first
rows; its relaxation concerns their support sizes. The raw sharp theorem
currently retains the all-first-row braid assumption. These two scopes must
not be conflated.

## Independent declarations and limitations

`SharpAudit.raw_nine_array_sharp_bounds` expands all nine original parameter
arrays, every ReLU in the forward pass, and the signed-neighbor count. It
checks the sharper integer and real conclusions without assuming coverage,
capacity, or a structural matching obstruction. The separate
`normalized_feeding_exact_type` exposes the precise normalization and
feeding-only support assumptions.

Both independent contracts passed Lean with exit code zero and only the
standard three axioms. The same run audited the sharpened connected-set
count, two-component count, and exponential arithmetic. A separate
union-find implementation in `sharp_graph_controls.py` checked both sharp
graph inequalities on all 2,164 degree-two graphs through six vertices and
all 127,739 of their subsets. This differs from the earlier BFS instrument;
these finite controls do not replace the universal Lean proofs.

The result remains restricted to degree-two interaction graphs. It does not
settle the unrestricted quadratic-first-width problem. This audit adds no
all-arity existence theorem for the restricted class; the earlier literal
MAX_4 control and its graph-degree verification remain unchanged. Final Lean
type/axiom evidence belongs to the content-bound verification receipt.
