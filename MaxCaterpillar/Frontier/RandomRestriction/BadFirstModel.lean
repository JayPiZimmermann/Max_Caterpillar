import MaxCaterpillar.Frontier.RandomRestriction.BadFirst
import MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction.ModelStats

/-! # The first exceptional event of the actual indexed normalized network -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.BadFirst
variable {N h₁ h₂ : ℕ}

/-- Every original first hidden index is included, with no readout filter. -/
@[simp] theorem largeSupportCount_rowSupport (net : NormalizedNetwork N h₁ h₂) :
    largeSupportCount (fun j => NormalizedNetwork.rowSupport (net.A j)) =
      ActualHalfRestriction.nonBraidCount net := rfl

noncomputable def modelBadFirstEvent (net : NormalizedNetwork N h₁ h₂) :
    Finset (Equiv.Perm (Fin N)) :=
  badFirstEvent (fun j => NormalizedNetwork.rowSupport (net.A j))

theorem modelBadFirstEvent_card_mul_le (hN : 5 ≤ N)
    (net : NormalizedNetwork N h₁ h₂) :
    (modelBadFirstEvent net).card * N.descFactorial 3 ≤
      60 * ActualHalfRestriction.nonBraidCount net * Fintype.card (Equiv.Perm (Fin N)) := by
  simpa only [modelBadFirstEvent,largeSupportCount_rowSupport] using
    badFirstEvent_card_mul_le hN (fun j => NormalizedNetwork.rowSupport (net.A j))

theorem modelBadFirstEvent_fraction_le (hN : 5 ≤ N)
    (net : NormalizedNetwork N h₁ h₂) :
    ((modelBadFirstEvent net).card : ℝ) / Fintype.card (Equiv.Perm (Fin N)) ≤
      60 * (ActualHalfRestriction.nonBraidCount net : ℝ) / (N.descFactorial 3 : ℝ) := by
  simpa only [modelBadFirstEvent,largeSupportCount_rowSupport] using
    badFirstEvent_fraction_le hN (fun j => NormalizedNetwork.rowSupport (net.A j))

theorem modelBadFirstEvent_card_four_mul_le (hN : 5 ≤ N)
    (net : NormalizedNetwork N h₁ h₂)
    (hbudget : 240 * ActualHalfRestriction.nonBraidCount net ≤ N.descFactorial 3) :
    4 * (modelBadFirstEvent net).card ≤ Fintype.card (Equiv.Perm (Fin N)) := by
  apply badFirstEvent_card_four_mul_le hN
  simpa only [largeSupportCount_rowSupport] using hbudget

#print axioms modelBadFirstEvent_card_mul_le
#print axioms modelBadFirstEvent_card_four_mul_le
end MaxCaterpillar.Frontier.RandomRestriction.BadFirst
