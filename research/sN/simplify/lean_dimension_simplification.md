# Factorial dictionary-dimension proof: simplification pass

The proof still establishes exactly `Dimension.factorial_le_quotientDim`:
for every `r ≥ 1`, the dictionary quotient has dimension at least `r!`.
No definition, theorem statement, hypothesis, or public declaration changed.
All 41 declaration headers agree with the baseline (`e1ebfc0`).
The module goes from 402 to 380 lines.

## Changes

- A permutation without an adjacent descent is monotone. Mathlib's
  `Monotone.strictMono_of_injective` now supplies strict monotonicity at once;
  the proof no longer establishes strictness at every adjacent pair.
- The relative order `ρ⁻¹π` remains a `PathIdx`. Its existing middle-label
  preservation proves the first endpoint condition, while a descent cannot
  land at the last label. This removes repeated natural-number endpoint
  arithmetic from `detector_other`.
- The detector is descended directly to the quotient using `Submodule.liftQ`.
  Applying that linear functional to a relation isolates its coefficient.
  There is no longer a detour through quotient-zero membership and coercions
  of sums back to the ambient function space.
- The off-diagonal detector's inequalities use only their three required
  facts, and the same sum bound is reused through the final positivity step.

## Routes compared

**Keep the finite mixed-difference detector.** It evaluates the Kronecker
pairing exactly on eight corners and kills the auxiliary space without
introducing differential or polytope machinery. Replacing it with the paper's
one-germ proof would introduce extra formal definitions and bridges while
leaving the same path-order/descent argument to prove. No shorter verified
replacement for the detector itself was found in this pass.

**Direct quotient duality replaces membership bookkeeping.** Rather than
construct a full map to the coordinate vector space and prove its
surjectivity, descend one already available detector at a time. This is the
same dual-basis argument with less formal infrastructure and preserves the
original finite-dimensional linear-independence theorem.

## Verification

`dimension_refactor/Check.lean` checks the exact types of the three changed
proofs and the unchanged self-detector (`exists_descent`, `detector_self`, `detector_other`, and
`factorial_le_quotientDim`) and prints their transitive axioms.
The final receipt records source hashes, commands, and exit statuses.
The parent task separately handles reverse consumers and the public gate.

Baseline exact-file compile: 7.98 s. First successful refactor compile:
6.49 s. These are single observations, not a benchmark. Commands use
`scripts/lean_lock.sh`; elapsed time in later runs can include lock waiting.

The intermediate `final_build.log` and `final_build2.log` record failed
attempts to shorten the self-detector's index arithmetic using `omega`.
That cosmetic shortcut was discarded; the already verified proof remains. `exact_check.log` ran before a fresh module artifact
existed and is explicitly not evidence for the replacement proof. Only the
fresh successful module build and its subsequent exact check are consumed.
