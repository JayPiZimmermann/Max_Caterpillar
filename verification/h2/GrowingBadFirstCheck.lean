import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirstConfigurations

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirst
variable {n k m : ℕ} {κ : Type*} [Fintype κ]
example (hkn : k ≤ n) (T : κ → Finset (Fin n)) :
    (badFirstEvent k T).card * n.descFactorial 3 ≤
      largeSupportCount T * k.descFactorial 3 * Fintype.card (Equiv.Perm (Fin n)) :=
  badFirstEvent_card_mul_le hkn T
example (hkn : k ≤ n) (hn : 3 ≤ n) (T : κ → Finset (Fin n)) :
    ((badFirstEvent k T).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) ≤
      (largeSupportCount T : ℝ) * (k.descFactorial 3 : ℝ) / (n.descFactorial 3 : ℝ) :=
  badFirstEvent_fraction_le hkn hn T
example (hkn : k ≤ n) (hk : k < 3) (T : κ → Finset (Fin n)) :
    badFirstEvent k T = ∅ := badFirstEvent_empty_of_arity_lt_three hkn hk T
example (T : Fin 0 → Finset (Fin n)) : badFirstEvent k T = ∅ := by
  ext σ
  simp [mem_badFirstEvent]
example (hn : 3 ≤ m+k) (T : κ → Finset (Fin (m+k))) :
    ((configurationBadFirstEvent k m T).card : ℝ) /
      Fintype.card (Configurations.Configuration k m) ≤
    (largeSupportCount T : ℝ) * (k.descFactorial 3 : ℝ) / ((m+k).descFactorial 3 : ℝ) :=
  configurationBadFirstEvent_fraction_le k m hn T

#check @badFirstEvent_fraction_le
#check @configurationBadFirstEvent_fraction_le
#print axioms support_containment_card_mul_le
#print axioms badFirstEvent_card_mul_le
#print axioms badFirstEvent_fraction_le
#print axioms badFirstEvent_empty_of_arity_lt_three
#print axioms badFirstEvent_card_four_mul_le
#print axioms mem_configurationBadFirstEvent
#print axioms configurationBadFirstEvent_fraction_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirst
