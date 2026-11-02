import MaxCaterpillar.Frontier.RandomRestriction.BraidCoinColumn
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.Linearization
import MaxCaterpillar.Frontier.RandomRestriction.CoinRank

/-! # Exact effective-row differences, retaining every indexed parallel row

An actual activation difference supported on one coordinate pair aggregates
to the signed edge weight. Both the row and activation assumptions are explicit;
the identity is derived from the original real weights and coefficient rows.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators DominantGap NormalizedNetwork
variable {N h₁ h₂ : ℕ}

theorem effectiveRow_eq_coin_sum (net : NormalizedNetwork N h₁ h₂)
    (b : Fin h₁ → Bool) (k : Fin h₂) :
    effectiveRow net b k = net.U k +
      ∑ j, coinCoefficient (b j) • (net.W k j • net.A j) := by
  classical
  rw [effectiveRow, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  cases hb : b j <;> simp [hb, coinCoefficient]

theorem effectiveRow_sub (net : NormalizedNetwork N h₁ h₂)
    (b b' : Fin h₁ → Bool) (k : Fin h₂) :
    effectiveRow net b' k - effectiveRow net b k =
      ∑ j, net.W k j • ((coinCoefficient (b' j) - coinCoefficient (b j)) • net.A j) := by
  rw [effectiveRow_eq_coin_sum, effectiveRow_eq_coin_sum]
  simp_rw [sub_smul, smul_sub, smul_comm (net.W k _) (coinCoefficient _) ]
  rw [Finset.sum_sub_distrib]
  abel

/-- Only feeding rows matter; all signs and all parallel rows are retained.
The hypothesis supplies individual actual gate changes, rather than a graph
column identity. -/
theorem effectiveRow_sub_eq_braidCoinColumn (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (k : Fin h₂) (b b' : Fin h₁ → Bool)
    (a c : Fin N) (hac : a ≠ c) (t : ℝ)
    (hpair : ∀ j, rowSupport (net.A j) ⊆ {a,c} →
      coinCoefficient (b' j) - coinCoefficient (b j) = t * edgeCoinDifference (net.A j) a c)
    (hother : ∀ j, net.W k j ≠ 0 → ¬rowSupport (net.A j) ⊆ {a,c} → b' j = b j) :
    effectiveRow net b' k - effectiveRow net b k =
      t • (-braidEdgeWeight net.A (net.W k) a c • braidRoot a c) := by
  classical
  rw [effectiveRow_sub]
  have hf : (∑ j, net.W k j •
      ((coinCoefficient (b' j) - coinCoefficient (b j)) • net.A j)) =
      ∑ j in Finset.univ.filter (fun j => rowSupport (net.A j) ⊆ {a,c}),
        net.W k j • ((t * edgeCoinDifference (net.A j) a c) • net.A j) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hs : rowSupport (net.A j) ⊆ {a,c}
    · rw [if_pos hs, hpair j hs]
    · rw [if_neg hs]
      by_cases hW : net.W k j = 0
      · rw [hW, zero_smul]
      · rw [hother j hW hs, sub_self, zero_smul, smul_zero]
  rw [hf]
  calc
    _ = t • (∑ j in Finset.univ.filter (fun j => rowSupport (net.A j) ⊆ {a,c}),
        net.W k j • (edgeCoinDifference (net.A j) a c • net.A j)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_smul, smul_comm (net.W k j) t]
    _ = t • ((∑ j in Finset.univ.filter (fun j => rowSupport (net.A j) ⊆ {a,c}),
        net.W k j * |net.A j a|) • braidRoot a c) := by
      rw [sum_edgeCoinDifference_smul net.A (net.W k) _ a c hac
        (fun j _ => hn.1 j) (fun j hj => (Finset.mem_filter.mp hj).2)]
    _ = _ := by
      rw [sum_supported_abs_eq net.A (net.W k) a c hac hn.1]
      simp only [braidEdgeWeight, neg_neg]

#print axioms effectiveRow_eq_coin_sum
#print axioms effectiveRow_sub
#print axioms effectiveRow_sub_eq_braidCoinColumn
end MaxCaterpillar.Frontier.RandomRestriction
