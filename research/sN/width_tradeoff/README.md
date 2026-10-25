# Width-pair proof search: Lean-only results

The live question is whether the coordinate maximum has one pair of hidden
layer widths minimizing both coordinates, or whether increasing the first
width can strictly reduce the smallest attainable second width. **The
unrestricted max-five question is still open.** Incomparable constructions
alone do not prove a tradeoff.

All results below concern `MaxCaterpillar.Network`, with arbitrary real
parameters and biases, no skip connections, and equality at every real
input. Constructive witnesses additionally have the stated rationality and
bias properties. Only checked Lean declarations count as evidence in this
record. Older numerical or externally certified investigations are not
included in these bounds. No result from this search has been added to the
paper; GitHub Actions remains disabled.

## A complete negative answer for general CPWL functions

For the one-dimensional tent

\[
T(x)=\sigma(x)-2\sigma(x-1)+\sigma(x-2),
\]

the exact feasible region is

\[
(h_1\ge1\ \text{and}\ h_2\ge2)
\quad\text{or}\quad
(h_1\ge2\ \text{and}\ h_2\ge1).
\]

Thus its two Pareto-minimal pairs are `(1,2)` and `(2,1)`. The minimum
second width is two at first width one and one at every first width at
least two. No network attains both separate coordinate minima.

The explicit identities are

\[
T(x)=\sigma(2-\sigma(x))-2\sigma(1-\sigma(x)),\qquad
T(x)=\sigma\bigl(\sigma(x)-2\sigma(x-1)\bigr).
\]

Every scalar network with widths `(1,1)` is monotone or antitone, whereas
the tent takes values `0,1,0` at `0,1,2`. A zero hidden width gives a
constant. These arguments and zero padding prove the entire frontier in
[`AuditTent.lean`](AuditTent.lean), declaration `tent_widths_iff`.
[`Checks.lean`](Checks.lean) connects it to `StrictTradeoff` and proves
`tent_has_no_leastPair`. This is a counterexample to a general least-pair
principle; it is **not** a counterexample for the coordinate maximum.

## What is proved for the maximum

- `max3_widths_iff` and `max4_widths_iff` already prove the simultaneous
  least pairs `(4,3)` and `(6,3)`. Their exact types and axioms were checked
  again locally.
- [`LowerFirst.lean`](LowerFirst.lean) proves the new uniform consequence
  `N+2 <= h1` for `N>=4`, with no restriction on the second hidden layer.
  The proof applies the existing first-layer rigidity lemma at the
  extremal row count. In particular, `h1>=7` at five inputs.
- The existing
  [`network_second_width_half_plus_one`](../frontierN/overnight_general_antipodal.lean)
  was recompiled and audited: `N+2 <= 2*h2` for every positive arity and
  every first width. In particular, `h2>=4` at five inputs.
- [`UpperMax5.lean`](UpperMax5.lean) proves an actual `Network 5 10 6`,
  rational weights, zero biases. It compresses the first layer of the
  existing global identity by hinge reversal and accounts explicitly for
  the two remainder neurons. It uses no uncounted linear skip.
- [`UpperNineNetwork.lean`](UpperNineNetwork.lean) proves an actual
  `Network 5 9 14`, also with rational weights and zero biases. The global
  identity is proved in Lean on all 120 closed coordinate orders and an
  exhaustive order split proves coverage. Each case uses algebraic ReLU
  identities and exact inequalities. `upper_gen_nine.py` emits the Lean
  source; the kernel checks every case and the network bridge. Neither
  the generator's arithmetic nor any external certificate is evidence.

Consequently the separate max-five minima currently satisfy the
Lean-verified bounds `7 <= min h1 <= 9` and `4 <= min h2 <= 6`.
The two upper witnesses `(9,14)` and `(10,6)` remain incomparable upper
bounds. No exclusion of `(9,6)` has been proved in this batch.

The older claim that first width nine is minimal depends on an
unformalized classification bridge. It is not a Lean-verified lower
bound in this record. Likewise, the externally certified fixed-P4
second-width-seven exclusion is not used here.

## Exact logical form of the two search targets

[`Frontier.lean`](Frontier.lean) defines `Feasible`, `LeastPair`,
`StrictTradeoff`, and `ParetoPair` directly using `Network.eval`.
It proves, for every representable target:

1. Feasibility is upward closed under increasing either hidden width.
2. Both separate coordinate minima are attained, possibly by different
   networks.
3. A least pair exists exactly when the feasible region is a rectangle
   above that pair.
4. The absence of a least pair is equivalent to two attained incomparable
   pairs whose southwest corner is infeasible.
5. The minimum second width eventually stabilizes as the first width
   increases. Every feasible pair dominates a Pareto-minimal pair, and
   all Pareto pairs lie in one finite rectangle.

These statements do not determine which alternative holds for max-five.
The precise unresolved goals are `StrictTradeoff (Maximum 5)` and its
opposite `exists a b, LeastPair (Maximum 5) a b`. A possible constructive
branch is an exact `(9,6)` network, but that alone would still require
matching unrestricted lower bounds to prove a least pair.

## Lower-bound branch and a formally refuted shortcut

[`LowerTransverse.lean`](LowerTransverse.lean) proves that independently
variable linear shifts in a globally nonnegative sum of ReLU differences
force each continuous preactivation to have a fixed weak sign on the
common shift kernel. The declaration `normalized_tails_kernel_odd`
applies this to two explicitly assumed normalized translation identities.
It proves that their represented function has a linear odd part on that
kernel.

The independence hypothesis is essential. The same file proves that two
equal shifts with opposite coefficients can cancel identically while
their common preactivation has both signs on the kernel. Dropping
independence is therefore a refuted route, not a remaining Lean tactic
problem. The surviving lemma does not exclude all width-four networks:
the actual-network normalization and dependent-shift cases remain
unresolved. No unrestricted `h2>=5` theorem is claimed.

## Verification

The exact-type checks are in `Checks.lean`. Every audited declaration uses
only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or
`Lean.ofReduceBool` is permitted. This is a research-owned collection,
not a replacement for the public verification manifest. All compilation
is local. Source reviews are in `audit_review.md`; detailed failed-route
records are in `lower_search.md`.

To reproduce the complete local proof build and exact-declaration checks:

```sh
bash research/sN/width_tradeoff/verify.sh
```

This compiles only the research leaves and their aggregation, using the
repository's installed dependencies, and checks every printed axiom list.
It records exit codes and source hashes in `verification/`. The existing
project dependencies must have been built locally. No numerical solver,
network training, remote build, or GitHub operation is involved.
