# Rational weights simplification — progress

## Step 1 (read)
- Current route: caterpillar_net -> maximum_width_one_basis (OneBasis) -> quotient_compression
  (Quotient.lean, basis extension + exists_rat_coeff_of_mem_span) -> Rationality.lean
  (rows_span_top / coeff_mem_ratField / independent_on_ratPoints / exists_rat_coeff_of_mem_span,
  ~185 lines of the 252) + compile_expansion_width.
- Idea chosen: a Q-linear projection pi : R -> Q with pi(q) = q (left inverse of Q -> R,
  Mathlib `LinearMap.exists_leftInverse_of_injective`). Applying pi to the identity at rational
  points rationalizes ANY real expansion on the same support; density + continuity finish.
  No basis, no independence, no row-span argument.
- Lean plan: Simplify/Rational.lean: generic lemma (~25 lines) + direct assembly using
  K = essentialKeys(normalizedKeys r) (bypasses quotient_compression's basis extension).

## Step 2 (Lean) — DONE
- MaxCaterpillar/Simplify/Rational.lean compiles (lake build MaxCaterpillar.Simplify.Rational OK).
- caterpillar_net_v4 : type rfl-equal to caterpillar_net; axioms propext, Classical.choice, Quot.sound.
- exists_rat_coeff_of_mem_span_v4: 31 lines vs 183 (and drops DecidableEq).
## Step 3 (write-up) — DONE: research/sN/simplify/rational.md
