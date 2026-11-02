import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirst
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations

/-! # Exact lift of the first exceptional event to actual three-permutation configurations -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirst
variable {κ : Type*} [Fintype κ]

noncomputable def literalBadFirstEvent (k m : ℕ) (T : κ → Finset (Fin (m+k))) :
    Finset (Configurations.LiteralConfiguration k m) := by
  classical
  exact (badFirstEvent k T) ×ˢ (Finset.univ : Finset (Configurations.RankPerm m))

noncomputable def configurationBadFirstEvent (k m : ℕ) (T : κ → Finset (Fin (m+k))) :
    Finset (Configurations.Configuration k m) :=
  Configurations.pullbackEvent (literalBadFirstEvent k m T)

/-- Neither the independent tail permutation nor the ranks alter selection. -/
@[simp] theorem mem_configurationBadFirstEvent (k m : ℕ)
    (T : κ → Finset (Fin (m+k))) (ω : Configurations.Configuration k m) :
    ω ∈ configurationBadFirstEvent k m T ↔
      ∃ j, 3 ≤ (T j).card ∧ T j ⊆ GoodEvent.smallRankGaps ω.1 k := by
  classical
  simp only [configurationBadFirstEvent,Configurations.mem_pullbackEvent,
    literalBadFirstEvent,Finset.mem_product,Finset.mem_univ,and_true,mem_badFirstEvent]
  have he := Configurations.selectedLabels_effective ω.1 ω.2.1
  change GoodEvent.smallRankGaps (Configurations.effectivePermutation ω.1 ω.2.1) k =
    GoodEvent.smallRankGaps ω.1 k at he
  simp only [Configurations.effectiveConfiguration,he]

theorem literalBadFirstEvent_fraction (k m : ℕ) (T : κ → Finset (Fin (m+k))) :
    ((literalBadFirstEvent k m T).card : ℝ) /
      Fintype.card (Configurations.LiteralConfiguration k m) =
    ((badFirstEvent k T).card : ℝ) / Fintype.card (Equiv.Perm (Fin (m+k))) := by
  rw [literalBadFirstEvent,Finset.card_product,Finset.card_univ,Fintype.card_prod,Nat.cast_mul,Nat.cast_mul]
  apply mul_div_mul_right
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Configurations.RankPerm m) ≠ 0)

/-- The full actual configuration fraction equals the original sigma-only fraction. -/
theorem configurationBadFirstEvent_fraction (k m : ℕ) (T : κ → Finset (Fin (m+k))) :
    ((configurationBadFirstEvent k m T).card : ℝ) /
      Fintype.card (Configurations.Configuration k m) =
    ((badFirstEvent k T).card : ℝ) / Fintype.card (Equiv.Perm (Fin (m+k))) := by
  rw [configurationBadFirstEvent,Configurations.pullbackEvent_fraction,literalBadFirstEvent_fraction]

theorem configurationBadFirstEvent_fraction_le (k m : ℕ) (hn : 3 ≤ m+k)
    (T : κ → Finset (Fin (m+k))) :
    ((configurationBadFirstEvent k m T).card : ℝ) /
      Fintype.card (Configurations.Configuration k m) ≤
    (largeSupportCount T : ℝ) * (k.descFactorial 3 : ℝ) / ((m+k).descFactorial 3 : ℝ) := by
  rw [configurationBadFirstEvent_fraction]
  exact badFirstEvent_fraction_le (Nat.le_add_left k m) hn T

#print axioms mem_configurationBadFirstEvent
#print axioms configurationBadFirstEvent_fraction
#print axioms configurationBadFirstEvent_fraction_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirst
