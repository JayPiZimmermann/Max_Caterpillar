# Overnight lower-bound search, 3 November 2026

This is the research queue for the requested overnight run, starting at
00:00 Europe/Berlin and targeting 08:00. The objective is stronger exact
MAX_N second-hidden-layer lower bounds, with special attention to weakening
the quadratic first-hidden-layer assumption. A route in this table is a
research proposal, not a proved result. Each branch must finish with an exact
proof, a reproducible refutation, or a precise residual.

## Screening and priorities

The 30 routes below survived an initial relevance and falsification screen:
each changes a load-bearing estimate, structural lemma, or model assumption;
has a concrete first test; and could improve a bound or remove a hypothesis.
They are not all independent conjectures, and several can combine. Existing
results are cited as inputs rather than rediscovered claims.

Excluded before selection: Boolean-only certificates; localization-only
induction that accepts the known five-input fake; unitwise forest-to-anchor-r
decomposition; fixed finite canonical dictionaries for arbitrary weighted
neurons; a worst-order rank proportional to matching number; and the refuted
inverse-square-root matching-partition peeling potential. Reopening any of
these requires a changed statement that excludes its recorded counterexample.

Priority A means a concrete proof mechanism or verified ingredient exists.
Priority B means a specific discriminating test should precede investment.
Priority C means a longer structural branch with a potentially large payoff.

## Thirty filtered routes

| # | Priority | Exact target and mechanism | First discriminating test | Potential benefit / remaining obstacle |
|---|---|---|---|---|
| 1 | A | Replace the affine Bernoulli wrapper's d=20C by the actual requirement 81h1 <= 4d² floor(N/2)². Choose d from an integer square root. | Compile the literal nine-array theorem at C=1 and at growing C; check floor and small-N boundaries. | Conditional exponent of order N^(3/2)/sqrt(h1), extending past quadratic h1. Growing structural H remains required. |
| 2 | A | Charge only original first-layer rows with a nonzero connection to a second neuron. Absorb output-only rows into auxiliary linear outer units. | Prove every auxiliary interaction graph is empty, so no selected matching witness or counted width is charged to it. | Arbitrarily many output-only first neurons become free in the conditional exponential tradeoff. |
| 3 | A | Replace total width by the actual weighted support cost after normalization/restriction. Keep non-braid count and falling fourth support moment separate. | Exhibit a family with very many braid rows and bounded non-braid cost; instantiate the existing finite transfer without h1. | Width-free structural assumptions can be much weaker than h1=O(N²); requires a faithful raw-array wrapper. |
| 4 | A | Use a small transversal of non-braid feeding supports: a generic top tie on its complement makes every touched row affine. | Prove the negative base point avoids all finitely many nonzero restricted covectors simultaneously; inspect cancellation and output-only rows. | Unconditional braid bounds on N minus transversal size, with no numerical cap on h1. |
| 5 | B | Optimize the retained-coordinate fraction rather than always retaining one half. Bound each support by its exact falling moment times its survival probability. | Optimize the exact finite rational expression, including the loss of input dimension; compare with the half restriction on supports 3 through 12. | Better constants and a cleaner h1/h2 tradeoff. Must prove one common restriction attains the needed joint budget. |
| 6 | B | Use nonuniform coordinate selection based on the non-braid support hypergraph, retaining a large independent or low-cost set. | Test weighted-star and disjoint-triple support hypergraphs, where uniform sampling has different losses. | Relaxes h1 through incidence structure; weighted selection must still support actual matching and tail probability estimates. |
| 7 | B | Merge positively proportional first-layer covectors before charging contamination, with signed downstream coefficients aggregated per second neuron. | Opposite orientations, exact cancellation, and zero aggregate coefficients are mandatory controls. | Replace neuron count by distinct effective hyperplanes without changing the represented function or original second width. |
| 8 | B | Separate a small collection of high-incidence supports, remove a few coordinates hitting them, and apply Bernoulli sampling to the residual hypergraph. | Compare with route 4 and a uniform family of disjoint supports; reject if the combined estimate never improves either endpoint. | An interpolating bound between a support transversal and a global width/moment budget. |
| 9 | A | Bound full signed-gradient atoms by resampling a vertex block, using nonzero-jump gap moments and read-degree Hölder, then regularize a matching core. | Independent audit of conditioning, gap-count moments, all-real coefficients, and the peeling deletion budget. | Candidate generic exp(-c nu/log nu) survival cost; conditional braid lower bound exp(cN/log N). |
| 10 | B | Replace uniform read-degree Hölder by fractional weights adapted to individual neighborhoods. | Optimize the finite fractional program on hub-plus-matching and nested-neighborhood graphs; verify moment exponents exactly. | Potential removal of the logarithm in route 9. A valid fractional cover alone need not give a large exponent. |
| 11 | B | Combine successive graph-regularization layers through conditional entropy or repeated decoupling instead of keeping only one layer. | Test dependencies on a layered graph with a large degree range; compare with a direct gradient-fiber histogram. | Another route to exp(-c nu), with the main danger being unjustified multiplication of correlated events. |
| 12 | B | Use the exact insertion-bit matrix and average 2^(-rank), exploiting all prefix equations. | Balanced signed complete bipartite graphs, including the grouped order of rank one, must pass. | A separate route to full-tail anti-concentration; randomness of the base order must pay for low-rank orders. |
| 13 | A | Fix a small set of exceptional edge orientations so the remaining graph is a forest or has one-sign weights. | Exact signed-cycle controls and the bound by 2^(number of exceptions) orientation patterns. | True exponential counting for near-forest or nearly one-sign original neurons, without width-inflating cycle expansion. |
| 14 | B | Charge only neurons on which the actual structural certificate functional is nonzero, instead of every graph outside C2. | Evaluate the new adaptive-selector logarithmic counterexample against the actual certificate score, not just top Möbius coefficient. | May recover cubic general-row transfer despite the raw C2-event cost barrier. Requires the functional, not just an existential obstruction. |
| 15 | B | Count selected matching witnesses and tail constraints jointly, using a generating function rather than a fixed witness plus a union bound. | Check the exact counterexample to the old matching-partition potential; the new inequality must not imply that refuted recursion. | Sharper constants or matching-size dependence; no automatic independence between selection and survival. |
| 16 | A | Complete exact cycle deletion, original-orientation three-state expansion, forest König, and the actual network lift. | Parallel/opposite first rows, signed cancellation, empty index families, and zero-sum heads. | Matching-r and cover-r finite function spans become equivalent at the same arity. Width expansion cannot be ignored in numerical bounds. |
| 17 | B | Seek a cover-two obstruction at a larger arity, such as 9 or 13, rather than insisting on the sharp seven-input threshold. | Full all-chamber finite-family tests with an exact MAX6 positive control; then derive a universal real-parameter certificate. | Any fixed-aritiy H(k,3) gives an unconditional cubic route through the existing matching machinery. Finite grids are not the theorem. |
| 18 | C | Extend the star certificate to arbitrary cover-two slopes, retaining all zero-support resonance faces and consistency equations. | Derive the full Real/Cons system before solving; compare the anchor-two specialization with Jensen's stated certificate. | A direct all-real SC2/H(7,3) proof, possibly computer-assisted. Parameter and resonance complexity is the obstacle. |
| 19 | C | Add Coxeter braid hexagon compatibility to the already understood commuting-swap rectangle relations. | Reject the known cube-local fake while preserving the exact MAX4 positive control. | A global conormal resolution theorem; local rectangle cancellation alone is known insufficient. |
| 20 | C | Prove a whole-network common-cover resolution after mixed creases cancel, allowing new weighted neurons. | Test whether the required kernel is generated globally, not in a fixed finite dictionary. | Could reduce a cover-two network to obstructions supported on a bounded union of centers. Unitwise splitting is false. |
| 21 | B | Use the valid relative decomposition forest-cover-r -> anchor-(r+1) plus low-rank terms, then prove a genuinely relative obstruction. | First test whether MAX5 already belongs to the star span modulo arbitrary lower-dimensional functions. | A shorter structural route if the quotient is strong enough; low-rank terms cannot simply be discarded. |
| 22 | C | Retain lower-dimensional strata in a recursive Fourier/residue or flag invariant, rather than only the generic top-dimensional transform. | Compare canonical star MAX5 exclusion and all-real weighted stars; inspect coordinate-flag false positives. | A cancellation-sensitive obstruction that could handle arbitrary heads and all forest shapes. |
| 23 | B | Extend the fixed-gauge weighted-star residue proof to interacting gauge packets and their circuit resonances. | Two distinct gauge packets with a shared projective pole; exact residue cancellation is the first test. | Continuous-family structural obstruction beyond finite coefficient grids; arbitrary gauge mixing remains substantial. |
| 24 | B | Exploit permutation representations to compress an all-real cover-two certificate into irreducible symmetry blocks. | Reconstruct the known star certificate with the compressed system and retain boundary orbits. | Makes larger all-real certificates feasible without mistaking symmetric test families for universal coverage. |
| 25 | B | Use exact multilevel input evaluations and mixed chamber jumps as a small certificate language. | Three-level inputs must reject the existing two-level-perfect star fake; signed mixed-ray mass must still be enforced. | A more economical universal checker than all chamber equations, if an actual completeness lemma can be proved. |
| 26 | A | Combine the new finite-difference rank obstruction with actual top-tie localization: every tied subset needs a neuron with at most two induced graph components. | Preserve original second-neuron indices and summed interaction graphs under localization. | Unconditional width bounds from graph coverage, without a growing H conjecture. |
| 27 | A | Count connected induced subsets for maximum-degree-two graphs and use route 26 at a central binomial arity. | Literal path/cycle/disconnected/isolate controls; a factor-two capacity loss is acceptable. | Unconditional 2^N/poly(N) second width for this explicit all-real graph class. Does not settle hub-heavy graphs. |
| 28 | B | Combine bounded-degree tie coverage with a separate small-center obstruction for hub-heavy units. | Double-stars with arbitrary heads are the mandatory difficult control; do not assume graph degree alone excludes them. | A structural dichotomy that might extend an unconditional exponential result toward unrestricted braid neurons. |
| 29 | A | Sharpen the q=2 envelope using the exact maximum of y² exp(-y), and replace raw fourth powers by falling fourth moments in the half restriction. | Rational upper bounds, all small support sizes, floor effects, and the original raw nine-array theorem. | A substantial unconditional quadratic constant improvement without changing any model assumptions. |
| 30 | B | Combine several fixed-arity bounds and the linear bound with an optimized finite crossover, instead of a single conservative large-N cutoff. | Exact finite arithmetic over the crossover range; verify the chosen constant uniformly for N>=3. | Better all-N quadratic constants and simpler final hypotheses; cannot improve the asymptotic exponent on its own. |

## Additional routes admitted after the first tests

These emerged during the run and are separate from the initial count of 30.

| # | Priority | Target | Discriminator and payoff |
|---|---|---|---|
| 31 | A | Global support-hypergraph alteration: retain Np minus the sum of p to each relevant support size, by removing one coordinate from each remaining bad support. | Prove the repair and expectation for actual row supports, then use the actual braid restriction. Large minimum support can permit polynomially or exponentially many first rows while retaining a linear-size MAX problem. The all-real raw model bridge now passes Lean. |
| 32 | B | Preserve both sides of a twice-resampled gradient event. The four-copy rectangle gives p^4 <= E[4^(-rank M)] for a weighted random interval-interlacement matrix. | A linear expected-rank bound would suffice via bounded differences. This changes the dependence information retained, unlike reoptimizing scalar Hölder after its hierarchical-graph barrier. |
| 33 | A | Use each original second neuron's support-union graph: connect coordinates occurring together in any feeding first row. | Generic tie localization plus the finite-difference obstruction should again force at most two components. This extends bounded-degree counting to arbitrary first covectors and biases, with no first-width cap; it deliberately uses a different graph from summed signed braid interactions. |
| 34 | B | Force a prescribed edge directly in a uniform partial matching, with a weighted transition kernel that changes its edge count by at most two. | Exact small-matching enumeration must prove the conditional uniform law before any moment estimate is imported. A valid coupling would improve the Laplace constant used by the unrestricted quadratic bound. |
| 35 | B | Encode connected induced sets by a spanning-tree contour: backward steps are forced, so only k-1 forward neighbor choices are charged. | Prove a literal injective finite encoding with at most 4^(k-1) Delta^(k-1) codes. Combined with actual tie coverage, this gives an unconditional exp(cN/Delta) bound without an analytic generating-series proof. |

Coordinate identification was also tested, but is not added as a stronger
dimension route: choosing one representative per block proves that its braid
criterion already implies a same-size valid generic deletion. Its exact
network pullback remains a useful verified model bridge.

## Depth-first execution and evidence

Immediate branches: 1–4, 9, 16–20, 26–27, and 29. Longer alternatives
10–12 and 21–24 run in parallel with independent audits. Each owner records
the first unresolved lemma and its cheapest counterexample test before
extending the proof. A failed lemma closes that branch until its statement
changes; it does not invalidate unrelated verified inputs.

All six project Claude skills were reread at the start of this run.
Published production sources remain frozen while new proofs are developed
in research leaves. Public promotion requires exact theorem types, actual
model bridges, nonvacuity where relevant, standard-axiom checks, source-bound
receipts, and a committed reproducible closure.

The overnight run is an active research objective, not a promise that an
unconditional exponential theorem must exist. The best published unconditional
general bound remains the checkpoint's quadratic bound until a stronger
actual theorem passes those checks.
