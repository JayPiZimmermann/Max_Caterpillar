import MaxCaterpillar.Frontier.RandomRestriction.CoinUniformity
import Mathlib.Data.Fintype.Perm

/-!
# Local coins from disjoint pairs of actual tail positions

For a fixed disjoint matching of positions, swap the two labels at one pair.
The data retain the unordered labels at every pair and every unmatched label.
The coin is true when the smaller label occupies the first position.
This gives genuine permutation-space flip equivalences directly, without a
Cartesian-tree or run-interval bridge.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Matching

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

abbrev Data (ι : Type*) (m : ℕ) := (ι → Finset (Fin m)) × (Fin m → Option (Fin m))

def usedPositions (slot : (ι × Bool) ↪ Fin m) : Finset (Fin m) := Finset.univ.image slot

lemma slot_mem_used (slot : (ι × Bool) ↪ Fin m) (i : ι) (b : Bool) :
    slot (i, b) ∈ usedPositions slot :=
  Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, rfl⟩

lemma slot_cross_ne (slot : (ι × Bool) ↪ Fin m) (i q : ι) (hqi : q ≠ i) (b c : Bool) :
    slot (q, b) ≠ slot (i, c) :=
  fun he => hqi (congrArg Prod.fst (slot.injective he))

lemma slot_pair_ne (slot : (ι × Bool) ↪ Fin m) (i : ι) :
    slot (i, false) ≠ slot (i, true) := by
  intro he
  have h := congrArg Prod.snd (slot.injective he)
  exact Bool.false_ne_true h

def swapTau (slot : (ι × Bool) ↪ Fin m) (i : ι) (tau : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin m) := (Equiv.swap (slot (i, false)) (slot (i, true))).trans tau

@[simp] lemma swapTau_apply (slot : (ι × Bool) ↪ Fin m) (i : ι)
    (tau : Equiv.Perm (Fin m)) (p : Fin m) :
    swapTau slot i tau p = tau (Equiv.swap (slot (i, false)) (slot (i, true)) p) := rfl

@[simp] lemma swapTau_left (slot : (ι × Bool) ↪ Fin m) (i : ι) (tau : Equiv.Perm (Fin m)) :
    swapTau slot i tau (slot (i, false)) = tau (slot (i, true)) := by
  rw [swapTau_apply, Equiv.swap_apply_left]

@[simp] lemma swapTau_right (slot : (ι × Bool) ↪ Fin m) (i : ι) (tau : Equiv.Perm (Fin m)) :
    swapTau slot i tau (slot (i, true)) = tau (slot (i, false)) := by
  rw [swapTau_apply, Equiv.swap_apply_right]

lemma swapTau_other (slot : (ι × Bool) ↪ Fin m) (i q : ι) (hqi : q ≠ i)
    (b : Bool) (tau : Equiv.Perm (Fin m)) :
    swapTau slot i tau (slot (q, b)) = tau (slot (q, b)) := by
  rw [swapTau_apply, Equiv.swap_apply_of_ne_of_ne
    (slot_cross_ne slot i q hqi b false) (slot_cross_ne slot i q hqi b true)]

lemma swapTau_outside (slot : (ι × Bool) ↪ Fin m) (i : ι) (tau : Equiv.Perm (Fin m))
    (p : Fin m) (hp : p ∉ usedPositions slot) : swapTau slot i tau p = tau p := by
  have hl : p ≠ slot (i, false) := fun he => hp (he ▸ slot_mem_used slot i false)
  have hr : p ≠ slot (i, true) := fun he => hp (he ▸ slot_mem_used slot i true)
  rw [swapTau_apply, Equiv.swap_apply_of_ne_of_ne hl hr]

theorem swapTau_involutive (slot : (ι × Bool) ↪ Fin m) (i : ι) :
    Function.Involutive (swapTau slot i) := by
  intro tau
  apply Equiv.ext
  intro p
  change tau (Equiv.swap (slot (i, false)) (slot (i, true))
    (Equiv.swap (slot (i, false)) (slot (i, true)) p)) = tau p
  rw [Equiv.swap_apply_self]

def swapTauEquiv (slot : (ι × Bool) ↪ Fin m) (i : ι) :
    Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin m) where
  toFun := swapTau slot i
  invFun := swapTau slot i
  left_inv := swapTau_involutive slot i
  right_inv := swapTau_involutive slot i

def pairLabels (slot : (ι × Bool) ↪ Fin m) (tau : Equiv.Perm (Fin m)) (i : ι) :
    Finset (Fin m) := {tau (slot (i, false)), tau (slot (i, true))}

def outsideLabels (slot : (ι × Bool) ↪ Fin m) (tau : Equiv.Perm (Fin m)) :
    Fin m → Option (Fin m) :=
  fun p => if p ∈ usedPositions slot then none else some (tau p)

def recorded (slot : (ι × Bool) ↪ Fin m) (tau : Equiv.Perm (Fin m)) : Data ι m :=
  (pairLabels slot tau, outsideLabels slot tau)

def coins (slot : (ι × Bool) ↪ Fin m) (tau : Equiv.Perm (Fin m)) (i : ι) : Bool :=
  decide (tau (slot (i, false)) < tau (slot (i, true)))

theorem recorded_swapTau (slot : (ι × Bool) ↪ Fin m) (i : ι) (tau : Equiv.Perm (Fin m)) :
    recorded slot (swapTau slot i tau) = recorded slot tau := by
  apply Prod.ext
  · funext q
    by_cases hqi : q = i
    · subst q
      simp only [recorded, pairLabels, swapTau_left, swapTau_right]
      exact Finset.pair_comm _ _
    · simp only [recorded, pairLabels, swapTau_other slot i q hqi]
  · funext p
    by_cases hp : p ∈ usedPositions slot
    · simp only [recorded, outsideLabels, if_pos hp]
    · simp only [recorded, outsideLabels, if_neg hp, swapTau_outside slot i tau p hp]

theorem coins_swapTau (slot : (ι × Bool) ↪ Fin m) (i : ι) (tau : Equiv.Perm (Fin m)) :
    coins slot (swapTau slot i tau) = flipBit i (coins slot tau) := by
  funext q
  change decide (swapTau slot i tau (slot (q, false)) < swapTau slot i tau (slot (q, true))) =
    if q = i then !(decide (tau (slot (q, false)) < tau (slot (q, true))))
      else decide (tau (slot (q, false)) < tau (slot (q, true)))
  by_cases hqi : q = i
  · subst q
    rw [if_pos rfl, swapTau_left, swapTau_right]
    have hne : tau (slot (i, false)) ≠ tau (slot (i, true)) :=
      fun he => slot_pair_ne slot i (tau.injective he)
    by_cases hlt : tau (slot (i, false)) < tau (slot (i, true))
    · have hnot : ¬tau (slot (i, true)) < tau (slot (i, false)) := not_lt_of_ge (le_of_lt hlt)
      simp [hlt, hnot]
    · have hgt : tau (slot (i, true)) < tau (slot (i, false)) :=
        lt_of_le_of_ne (le_of_not_gt hlt) (fun he => hne he.symm)
      simp [hlt, hgt]
  · rw [if_neg hqi, swapTau_other slot i q hqi false, swapTau_other slot i q hqi true]

/-- Actual label transpositions give the genuine finite flip system. -/
def flipSystem (slot : (ι × Bool) ↪ Fin m) : CoinFlipSystem (recorded slot) (coins slot) where
  equiv := swapTauEquiv slot
  data_eq := recorded_swapTau slot
  coins_eq := coins_swapTau slot

theorem pattern_cards_equal (slot : (ι × Bool) ↪ Fin m) (u : Data ι m) (a b : ι → Bool) :
    (patternFiber (recorded slot) (coins slot) u a).card =
      (patternFiber (recorded slot) (coins slot) u b).card :=
  coin_pattern_cards_equal (recorded slot) (coins slot) (flipSystem slot) u a b

theorem fiber_card_eq (slot : (ι × Bool) ↪ Fin m) (u : Data ι m) (b : ι → Bool) :
    (dataFiber (recorded slot) u).card =
      2 ^ Fintype.card ι * (patternFiber (recorded slot) (coins slot) u b).card :=
  data_fiber_card_eq (recorded slot) (coins slot) (flipSystem slot) u b

#check @swapTau
#check @recorded_swapTau
#check @coins_swapTau
#check @flipSystem
#check @fiber_card_eq
#print axioms swapTau_involutive
#print axioms recorded_swapTau
#print axioms coins_swapTau
#print axioms flipSystem
#print axioms pattern_cards_equal
#print axioms fiber_card_eq
end MaxCaterpillar.Frontier.RandomRestriction.Matching
