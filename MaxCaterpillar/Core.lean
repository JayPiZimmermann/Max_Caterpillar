import MaxCaterpillar.Lemmas
import MaxCaterpillar.Asymptotics
import MaxCaterpillar.RationalWidth

/-! # Construction-level statements

Width asymptotics, the compilation theorem for arbitrary expansions, and
correctness of the canonical network. The public interface is `Theorems.lean`.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar

/-- The displayed width bounds grow quadratically and as `2^{O(N log N)}`,
respectively. The logarithmic formulation fixes the meaning of the latter. -/
theorem width_asymptotics :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => (firstWidth N : ℝ)) (fun N => (N : ℝ) ^ 2) ∧
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => Real.log (secondWidth N)) (fun N => (N : ℝ) * Real.log N) :=
  ⟨firstWidth_isBigO_square, log_secondWidth_isBigO_mul_log⟩

/-- **Compilation.** Any expansion of the maximum by normalized
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

/-- The canonical network of `Construction.lean` computes the maximum. -/
theorem network_correct (r : ℕ) (hr : 1 ≤ r) :
    ∀ x, (network r).eval x = Maximum (r + 1 + 1) x :=
  fun x => (network_eval_internal r x).trans (compactEssentialNetwork_computes r hr x)

end MaxCaterpillar
