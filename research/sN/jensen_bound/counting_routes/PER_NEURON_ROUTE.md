# Actual per-neuron count with constant 400

The concrete Lean target is `PerNeuron.neuron_event_card_le_four_hundred`.
Its sample space is the literal product of three independent finite uniform
permutation spaces, not an assumed conditional sampling law:

- a full label-to-position permutation `sigma` on `Fin (m+5)`;
- a tail-label order `tau` on `Fin m`;
- a gap-rank permutation `rho` on `Fin m`.

The event for original second-neuron index `k` requires the actual counted
support good event at the effective full order, enough isolated low-rank gaps,
actual `net.inner k (actualGapPoint ...) = 0`, and two disjoint edges of the
actual ambient braid interaction graph on the five selected labels.

For `m >= 400`, `K >= 4`, and `K <= m/100`, its literal cardinality satisfies

    K^2 * card(neuronEvent k) <= 400 * card(Configuration m).

The network coefficients are arbitrary reals. Translation normalization is
explicit; no MAX identity, star coefficient certificate, probability bound,
rank bound, or event-count conclusion is a hypothesis of this theorem. The
scale is one actual common generic gap scale. A separate theorem derives a
uniform threshold for every such real network, so a count theorem with an
existential threshold has no genericity hypothesis either.

## Proof and modelling bridges

Fix the full permutation and gap ranks. The retained gap set gives disjoint
adjacent tail-position pairs. Recording each unordered label pair and every
unpaired label gives actual permutation fibers. Actual pair swaps preserve
the recording and flip exactly one comparison coin. The comparison coins and
the recording determine the full tail permutation. These proved bijections
provide the finite fair-coin law on each real fiber.

The actual support good event implies `ActualClean`. This uses the original
first-row supports before collapsing the selected anchor; an original row
with support at least three cannot have an isolated retained dominant gap.
Cleanliness is invariant under actual local swaps. At the same actual common
scale, nonbraid feeding rows keep their activations under these swaps. The
remaining pair-supported rows contribute the actual summed signed braid
weights. The restricted actual effective row is therefore affine in the real
coins, with one root column for each retained pair. Nonzero columns have
disjoint coordinate supports and are linearly independent. Hence the actual
inner-zero fraction in a clean fiber is at most `2^(-chi)`, where `chi` counts
nonzero edges in that actual matching. Genericity proves the equivalence
between actual scalar inner vanishing and actual restricted row vanishing.

The clean event is discarded only after this conditional count. Consequently
no unproved independence or measurability of the more elaborate role good
event is used. The resulting tail sum is the actual matching moment in the
induced tail graph.

The actual partial-matching size-bias coupling yields

    E[(1/2)^X] <= exp(-(7/12) * J * tR / (m*(m-1))).

Here `J >= K/2` on the isolated-gap good event and `tR` is the ordinary edge
count of the actual induced tail graph. Deleting five selected vertices loses
at most `5*(m+4)` edges. The separately verified scalar estimate therefore
gives, for every fixed full permutation and rank permutation,

    (60*eta^2/m^4) * tailSurvivalCount <=
      (400/K^2) * card(TailPerm).

The selected two-disjoint-edge event has actual full-permutation fraction at
most `60*eta^2/m^4`. Summing the last display over selected full permutations
cancels that density. The zero-density case is proved separately by the same
generic finite averaging lemma: its selected event is empty. No division by
the number of ambient edges is used, and empty tail graphs are covered by the
all-graph matching theorem.

## Scope

This is the quantitative actual per-neuron bridge. The final network lower
bound additionally uses the independently proved actual structural witness,
coverage by the finite bad events, support budgets, and scalar cutoff choice.
Those conclusions are not built into this event or its count.

The bounded-size-bias Laplace principle is standard (Arratia--Baxendale,
arXiv:1306.0157, Proposition 4.1). The simplification here is its application to
the actual finite partial-matching coupling and the resulting constants,
replacing the earlier concentration argument.
