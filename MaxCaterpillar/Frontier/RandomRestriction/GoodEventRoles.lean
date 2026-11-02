import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Actual finite role spaces for the support-weighted good event

A/C roles consist of an ordered pair of disjoint unordered pairs. B roles
consist of an unordered pair followed by two distinct ordered outside labels.
The definitions are valid for every finite support, including size below four.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
open BigOperators

variable {α : Type*} [DecidableEq α]

/-- An unordered pair of distinct labels in the actual support. -/
abbrev PairRole (T : Finset α) := ↥(T.powersetCard 2)

/-- Ordered cherry/remainder roles, each an unordered pair, with disjoint labels. -/
abbrev ACRole (T : Finset α) := Σ P : PairRole T, PairRole (T \ P.val)

/-- Ordered distinct outside labels after an unordered cherry. -/
abbrev OutsideRole (T : Finset α) (P : PairRole T) :=
  Σ z : ↥(T \ P.val), ↥((T \ P.val).erase z.val)

/-- The unordered cherry together with ordered tail and selected labels. -/
abbrev BRole (T : Finset α) := Σ P : PairRole T, OutsideRole T P

lemma pairRole_subset {T : Finset α} (P : PairRole T) : P.val ⊆ T :=
  (Finset.mem_powersetCard.mp P.property).1

@[simp] lemma pairRole_card {T : Finset α} (P : PairRole T) : P.val.card = 2 :=
  (Finset.mem_powersetCard.mp P.property).2

def ACRole.cherry {T : Finset α} (R : ACRole T) : Finset α := R.1.val
def ACRole.other {T : Finset α} (R : ACRole T) : Finset α := R.2.val

lemma ACRole.cherry_subset {T : Finset α} (R : ACRole T) : R.cherry ⊆ T :=
  pairRole_subset R.1
lemma ACRole.other_subset {T : Finset α} (R : ACRole T) : R.other ⊆ T :=
  Finset.Subset.trans (pairRole_subset R.2) (Finset.sdiff_subset _ _)
@[simp] lemma ACRole.cherry_card {T : Finset α} (R : ACRole T) : R.cherry.card = 2 :=
  pairRole_card R.1
@[simp] lemma ACRole.other_card {T : Finset α} (R : ACRole T) : R.other.card = 2 :=
  pairRole_card R.2
lemma ACRole.disjoint {T : Finset α} (R : ACRole T) : Disjoint R.cherry R.other := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp (pairRole_subset R.2 hy)).2 hx

def BRole.cherry {T : Finset α} (R : BRole T) : Finset α := R.1.val
def BRole.tail {T : Finset α} (R : BRole T) : α := R.2.1.val
def BRole.selected {T : Finset α} (R : BRole T) : α := R.2.2.val

lemma BRole.cherry_subset {T : Finset α} (R : BRole T) : R.cherry ⊆ T :=
  pairRole_subset R.1
@[simp] lemma BRole.cherry_card {T : Finset α} (R : BRole T) : R.cherry.card = 2 :=
  pairRole_card R.1
lemma BRole.tail_mem {T : Finset α} (R : BRole T) : R.tail ∈ T :=
  (Finset.mem_sdiff.mp R.2.1.property).1
lemma BRole.tail_not_mem_cherry {T : Finset α} (R : BRole T) : R.tail ∉ R.cherry :=
  (Finset.mem_sdiff.mp R.2.1.property).2
lemma BRole.selected_mem {T : Finset α} (R : BRole T) : R.selected ∈ T :=
  (Finset.mem_sdiff.mp (Finset.mem_erase.mp R.2.2.property).2).1
lemma BRole.selected_not_mem_cherry {T : Finset α} (R : BRole T) : R.selected ∉ R.cherry :=
  (Finset.mem_sdiff.mp (Finset.mem_erase.mp R.2.2.property).2).2
lemma BRole.tail_ne_selected {T : Finset α} (R : BRole T) : R.tail ≠ R.selected :=
  (Finset.mem_erase.mp R.2.2.property).1.symm

@[simp] theorem card_pairRole (T : Finset α) :
    Fintype.card (PairRole T) = T.card.choose 2 := by
  rw [Fintype.card_coe,Finset.card_powersetCard]

@[simp] lemma pairRole_complement_card {T : Finset α} (P : PairRole T) :
    (T \ P.val).card = T.card - 2 := by
  rw [Finset.card_sdiff (pairRole_subset P),pairRole_card]

@[simp] lemma pairRole_erase_complement_card {T : Finset α} (P : PairRole T)
    (z : ↥(T \ P.val)) : ((T \ P.val).erase z.val).card = T.card - 3 := by
  rw [Finset.card_erase_of_mem z.property,pairRole_complement_card,Nat.sub_sub]

/-- This counts the actual Sigma type, with no ordering of either pair. -/
theorem card_acRole (T : Finset α) :
    Fintype.card (ACRole T) = T.card.choose 2 * (T.card - 2).choose 2 := by
  change Fintype.card (Σ P : PairRole T, PairRole (T \ P.val)) = _
  rw [Fintype.card_sigma]
  simp only [card_pairRole,pairRole_complement_card,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,Nat.cast_id]

@[simp] theorem card_outsideRole (T : Finset α) (P : PairRole T) :
    Fintype.card (OutsideRole T P) = (T.card - 2) * (T.card - 3) := by
  change Fintype.card (Σ z : ↥(T \ P.val), ↥((T \ P.val).erase z.val)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe,pairRole_erase_complement_card,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,Nat.cast_id,pairRole_complement_card]

/-- The two outside labels are ordered, in contrast to the cherry pair. -/
theorem card_bRole (T : Finset α) :
    Fintype.card (BRole T) = T.card.choose 2 * (T.card - 2) * (T.card - 3) := by
  change Fintype.card (Σ P : PairRole T, OutsideRole T P) = _
  rw [Fintype.card_sigma]
  simp only [card_outsideRole,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,card_pairRole]
  exact (Nat.mul_assoc _ _ _).symm

private lemma choose_two_mul_two (r : ℕ) : r.choose 2 * 2 = r.descFactorial 2 := by
  simpa only [show Nat.factorial 2 = 2 from rfl,mul_comm] using
    (Nat.descFactorial_eq_factorial_mul_choose r 2).symm

private lemma descFactorial_four_split_two (r : ℕ) :
    r.descFactorial 4 = r.descFactorial 2 * (r - 2).descFactorial 2 := by
  simp only [Nat.descFactorial,Nat.sub_zero,mul_one,Nat.sub_sub]
  norm_num <;> ring

/-- Four orderings of the two unordered pairs give the falling factorial. -/
theorem card_acRole_mul_four (T : Finset α) :
    Fintype.card (ACRole T) * 4 = T.card.descFactorial 4 := by
  rw [card_acRole]
  calc
    (T.card.choose 2 * (T.card - 2).choose 2) * 4 =
        (T.card.choose 2 * 2) * ((T.card - 2).choose 2 * 2) := by ring
    _ = T.card.descFactorial 2 * (T.card - 2).descFactorial 2 := by
      rw [choose_two_mul_two,choose_two_mul_two]
    _ = T.card.descFactorial 4 := (descFactorial_four_split_two _).symm

/-- Only the cherry is unordered in a B role. -/
theorem card_bRole_mul_two (T : Finset α) :
    Fintype.card (BRole T) * 2 = T.card.descFactorial 4 := by
  rw [card_bRole]
  calc
    (T.card.choose 2 * (T.card - 2) * (T.card - 3)) * 2 =
        (T.card.choose 2 * 2) * (T.card - 2) * (T.card - 3) := by ring
    _ = T.card.descFactorial 2 * (T.card - 2) * (T.card - 3) := by
      rw [choose_two_mul_two]
    _ = T.card.descFactorial 4 := by
      simp only [Nat.descFactorial,Nat.sub_zero,mul_one]
      ring

#print axioms card_acRole_mul_four
#print axioms card_bRole_mul_two
end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
