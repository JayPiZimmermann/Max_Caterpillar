# Independent semantic review of the frontier and transverse lemmas

Review scope: the complete current source of `Frontier.lean` and
`LowerTransverse.lean`, their printed axiom logs, the actual `Network.eval`
definition, and the padding theorem used by the frontier. This was a source
and log review, not an additional independent kernel run. No mathematical or
scope defect was found.

## Frontier

`Feasible` quantifies over the actual ordinary two-hidden-layer network,
including arbitrary real weights and biases and equality at every real input.
There is no free skip or uncounted feature. `feasible_mono` uses the proved
physical padding construction.

`LeastPair` means a single attained network pair that minimizes both widths
over every feasible network. `StrictTradeoff` includes two attained pairs and
the **infeasibility of their southwest corner**. Hence incomparable upper
bounds alone do not satisfy the definition. Padding also shows that a missing
corner rules out any smaller second width at that first width.

All uses of separate coordinate minima, the dichotomy, eventual stabilization,
and Pareto boundedness explicitly assume at least one feasible network. Natural
number minimization makes the two separate minima attained, without assuming
that they are attained together. The proof of the dichotomy tests exactly the
joint corner. The Pareto definition is the ordinary componentwise minimum
definition, and `pareto_below` minimizes a sum only within the given finite
southwest rectangle. `pareto_bounded` bounds the entire Pareto set using two
networks attaining the separate minima.

The maximum-three and maximum-four wrappers use the existing exact network
frontier theorems. The file does not assert a rectangular maximum-five frontier.

## Transverse restriction

The final theorem assumes two exact, global normalized identities for the
same function, odd-linearity of `u`, `v`, and each `w_i`, continuity of the
`w_i`, nonzero signed coefficients, and directions `y_i` satisfying

\[
\delta_j(y_i)=\mathbf1_{j=i}.
\]

This is an explicit independence hypothesis on the shifts. The proof does
not silently assume such directions exist for arbitrary network parameters.
Zero coefficients can in principle be removed in a separate reduction, but
that reduction is not asserted by this theorem.

Subtracting the identities gives the nonnegative sum
`sigma(-u)+sigma(-v)`. The linear term vanishes on the common shift kernel by
testing both signs of an input. A perturbation along `y_i` isolates precisely
one ReLU difference. Continuity preserves strict positivity or negativity in
a neighborhood, and both signs of the perturbation force incompatible slopes
if `w_i` changes sign on the kernel. Thus each outer ReLU restricts to its
argument or zero there. The represented function then has linear odd part on
that kernel. All zero-value boundary cases are allowed.

**This is not an unrestricted width-four exclusion.** The theorem has no
`Network` argument and supplies neither a reduction of every width-four
network to the assumed normalized identities nor treatment of dependent
shift families. Even after such a reduction, the resulting odd-linearity
restriction requires a further contradiction argument for the target.

The existing logs list only `propext`, `Classical.choice`, and `Quot.sound`
for the reviewed public conclusions. No numerical evidence was used in this
review, and no builds or logs owned by another agent were modified.

## Physical width of the two new maximum-five constructions

The complete `UpperMax5.lean` and `UpperNineNetwork.lean` network bridges,
and the consumed `network_of_rows` declaration in `SmallN/Common.lean`,
were also read independently. No modelling gap was found.

`rowsNet` uses exactly the declared first-layer rows. Its second layer
appends `R` and `-R` to the supplied outer rows and gives these two extra
neurons output weights `1` and `-1`. Consequently four supplied rows give
six physical second-layer neurons, and twelve supplied rows give fourteen.
The remainder `R` is a linear form in the counted first-layer ReLU features,
not an input skip or free output feature. The two added neurons implement it.
All three bias arrays are zero. All weights are rational because the explicit
arrays lie in the rationals and the bridge proves rationality of every entry.

`UpperMax5.lean` transfers the existing globally quantified five-input maximum
identity by exact algebraic normalization. `UpperNineNetwork.lean` transfers
its separately formalized global identity in the same manner. Neither final
network theorem assumes a numerical verdict or sampled identity. The owner's
final compilation and axiom audit of the nine-row identity closure are still
required before reporting that network as Lean verified; this source review
does not replace that gate.
