# Width tradeoff: Lean-only lower-bound search

The unrestricted question whether the least second width for max-five drops
when the first width increases remains open in this search. No numerical
search or external finite certificate is used in the results below.

## New checked statements

`LowerFirst.lean` proves, in the actual `Network` model with arbitrary real
weights and biases and no skips:

```
4 ≤ N → (∀ x, net.eval x = Maximum N x) → N + 2 ≤ h₁.
```

In particular, an exact max-five network has first hidden layer width at
least seven. This bound is independent of the second width. It follows
from the existing general Lemma M: at first width at most N+1, the rank
conditions at the two diagonal tails force one positive-sum row, one
negative-sum row, and exactly N nonnegative-sum rows. Lemma M excludes
that configuration for N≥4. The earlier production corollary had only
used this general lemma at N=4.

`LowerTransverse.lean` proves the finite-family transverse restriction.
Let δᵢ and L be linear forms, wᵢ continuous functions, and sᵢ nonzero real
coefficients. Assume

```
0 ≤ L(x) + Σᵢ sᵢ (σ(wᵢ(x)+δᵢ(x)) − σ(wᵢ(x)))  for every x.
```

If yᵢ satisfies δⱼ(yᵢ)=1 when j=i and zero otherwise, then wᵢ has one weak
sign throughout the common kernel of the δⱼ. Thus all the outer ReLUs
reduce to either zero or their arguments on that kernel. The proof keeps
zero boundaries and arbitrary coefficient signs.

`normalized_tails_kernel_odd` connects this restriction to the normalized
two-tail identities used in the second-width-four investigation. Assuming
those two functional identities, linear odd parts for the shallow
functions, and the independent-shift hypotheses above, the represented
function has a linear odd part on the common kernel. This is an analytic
necessary condition. It does not assert that every network has independent
shifts, and it does not exclude second width four.

The same file contains a Lean-checked counterexample to deleting the
independence hypothesis: equal shifts and equal preactivations with
opposite outer coefficients cancel identically, but the preactivation has
both signs on the common kernel. This blocks the proposed unrestricted
extension of this particular argument.

## Exact residuals

* A lower bound for one prescribed nine-row first layer is not an exclusion
  for every first layer of width nine.
* The cases of independent and dependent tail shifts must remain separate.
  The independent case now has the formal reduction above; the dependent
  case permits cancellation and needs a different argument.
* A kernel of dimension three on which max-five has linear odd part does
  not itself give a contradiction. The written equality-plane classification
  permits paired coordinates plus an interior fifth coordinate, and the
  restricted maximum is shallow. No unformalized classification is consumed
  by the new Lean theorems.
* Neither a genuine attained width tradeoff nor a simultaneous minimum pair
  for max-five was proved here.

## Reproduction and trust boundary

Run locally, from the repository root:

```
lake env lean -j1 research/sN/width_tradeoff/LowerFirst.lean
lake env lean -j1 research/sN/width_tradeoff/LowerTransverse.lean
```

Both commands exited zero. The adjacent `lower_first_compile.log` and
`lower_transverse_compile.log` contain the exact public theorem types and
axiom audits. Every reported theorem uses only `propext`, `Classical.choice`,
and `Quot.sound`. Both files disable automatic implicit variables. No
`sorry`, `native_decide`, or external solver verdict is used.

These are locally checked research leaves, not additions to the production
root or a clean committed public verification certificate. No GitHub build,
push, or manuscript edit was performed by this search branch.
