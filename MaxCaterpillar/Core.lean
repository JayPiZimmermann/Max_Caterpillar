import MaxCaterpillar.Lemmas
import MaxCaterpillar.Asymptotics
import MaxCaterpillar.RationalWidth

/-! # The public theorem interface

The new construction is nonrecursive data; its correctness proof uses
induction. The width claims include all correction units.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar

/-- Version 1 (retained backup): a real-parameter network.
For `N ≥ 3` this is `construction_width`; the arities `N ≤ 2` are covered
by the internal all-arity statement. -/
theorem maximum_width (N : ℕ) [NeZero N] :
    ∃ net : Network N (firstWidth N) (secondWidth N),
      ∀ x, net.eval x = Maximum N x := by
  rcases N with _ | _ | _ | r
  case succ.succ.succ => exact construction_width (r + 1) (Nat.le_add_left 1 r)
  all_goals exact Internal.secondWidth_eq _ ▸
    Internal.twoLayerWidth_iff.mp (Width.MAX_twoLayerWidth_caterpillar_spine_all _)

/-- The displayed width bounds grow quadratically and as `2^{O(N log N)}`,
respectively. The logarithmic formulation fixes the meaning of the latter. -/
theorem width_asymptotics :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => (firstWidth N : ℝ)) (fun N => (N : ℝ) ^ 2) ∧
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => Real.log (secondWidth N)) (fun N => (N : ℝ) * Real.log N) :=
  ⟨firstWidth_isBigO_square, log_secondWidth_isBigO_mul_log⟩

/-- Version 2 of the main theorem: the same widths with rational weights and
zero biases. For `N ≥ 3` the network is the Version 1 construction `network`,
whose canonical coefficients (an average over all bases) are proved rational
(`coefficient_rational`). Version 3, `maximum_width_one_basis` in
`OneBasis.lean`, proves the same statement from one basis. -/
theorem maximum_width_rational (N : ℕ) [NeZero N] :
    ∃ net : Network N (firstWidth N) (secondWidth N),
      (∀ x, net.eval x = Maximum N x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases := by
  rcases N with _ | _ | _ | r
  · exact absurd rfl (NeZero.ne 0)
  · exact maximum_width_rational_one
  · exact maximum_width_rational_two
  · exact maximum_width_rational_of_three_le (r := r + 1) (Nat.le_add_left 1 r)

/-- The canonical (Version 1) coefficients are rational. -/
theorem coefficient_rational (r : ℕ) (hr : 1 ≤ r) (i : Atom r) :
    ∃ q : ℚ, (q : ℝ) = coefficient r i :=
  mem_ratField_iff.mp (coefficient_mem_ratField hr i)

/-- The Version 1 network has rational weights and zero biases. -/
theorem network_rational (r : ℕ) (hr : 1 ≤ r) :
    (network r).HasRationalWeights ∧ (network r).HasZeroBiases :=
  ⟨network_hasRationalWeights hr, network_hasZeroBiases⟩

/-- Version 2 compilation theorem: any expansion of the maximum by normalized
face functions `K` and an auxiliary remainder with coefficient vector `a`
compiles with the existing first hidden layer and `|K| + 2` second-layer
neurons and zero biases; the weights are rational when `d` and `a` are. -/
theorem compilation (r : ℕ) (K : Finset (Caterpillar.Corrections.RealKey (r + 1)))
    (hK : K ⊆ Caterpillar.Corrections.normalizedKeys r)
    (d : Caterpillar.Corrections.RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x =
      ∑ k in K, d k * Caterpillar.Corrections.realUnitY k x + auxiliary a x) :
    ∃ net : Network (r + 1 + 1) (firstWidth (r + 1 + 1)) (K.card + 2),
      (∀ x, net.eval x = Maximum (r + 1 + 1) x) ∧ net.HasZeroBiases ∧
      ((∀ k ∈ K, ∃ q : ℚ, (q : ℝ) = d k) → (∀ j, ∃ q : ℚ, (q : ℝ) = a j) →
        net.HasRationalWeights) := by
  obtain ⟨net, heval, hz, hrat⟩ := compile_expansion K d a
    (fun k hk => Caterpillar.Corrections.normalizedKeys_simplexDifference k (hK hk)) h
  refine ⟨net, heval, hz, fun hd ha => hrat (fun k hk => ratVec_normalizedKey (hK hk))
    (fun k hk => mem_ratField_iff.mpr (hd k hk)) (fun j => mem_ratField_iff.mpr (ha j))⟩

/-- Version 2 coefficient rule: one basis of the dictionary gives rational
coefficients, without integration. -/
theorem rational_coefficients (r : ℕ) (hr : 1 ≤ r) :
    ∃ c : Atom r → ℝ, (∀ i, ∃ q : ℚ, (q : ℝ) = c i) ∧
      ∀ x, ∑ i, c i * atom r i x = Maximum (r + 1 + 1) x :=
  rational_expansion hr

theorem network_correct (r : ℕ) (hr : 1 ≤ r) :
    ∀ x, (network r).eval x = Maximum (r + 1 + 1) x :=
  fun x => (network_eval_internal r x).trans (compactEssentialNetwork_computes r hr x)

end MaxCaterpillar
