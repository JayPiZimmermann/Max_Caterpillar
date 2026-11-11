import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConfigurationsGeometry

/-! Literal selected/tail sum decomposition at arbitrary selected arity. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations
open BigOperators

lemma sum_full_positions {k m : ℕ} (f : Fin (m+k) → ℝ) :
    (∑ i,f i)=(∑ s : Fin k,f (selectedPosition k m s))+
      ∑ t : Fin m,f (tailPosition k m t) := by
  have h := Equiv.sum_comp (fullPositionEquiv k m) f
  simpa only [Fintype.sum_sum_type,fullPositionEquiv_selected,fullPositionEquiv_tail] using h.symm

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations
