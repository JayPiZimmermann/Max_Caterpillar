import MaxNN.Constructions.Paramid.Caterpillar.Block.Patterns
import MaxNN.Constructions.Paramid.Caterpillar.Formula.Values

/-! # Indices and active block fibres of the caterpillar formula -/

namespace MaxNN.Caterpillar

variable {r : ℕ}

abbrev BlockIndex (r : ℕ) :=
  Equiv.Perm (Fin (r + 1 + 1)) × {S : Finset (Fin (r + 1)) // S ∈ admissibleCuts r}

def blockWordValues (x : Fin (r + 1 + 1) → ℝ) (q : BlockIndex r) :
    Fin (r + 1) → ℝ :=
  fun i => x (q.1 i.succ)

def blockApexValue (x : Fin (r + 1 + 1) → ℝ) (q : BlockIndex r) : ℝ :=
  x (q.1 0)

def ActivePrefix (x : Fin (r + 1 + 1) → ℝ) (q : BlockIndex r) : Prop :=
  ∃ j : Fin r, (0 : Fin (r + 1)) < j.castSucc ∧ j.succ ∈ q.2.1 ∧
    SplitValues (blockWordValues x q) j ∧
    blockApexValue x q = blockWordValues x q j.succ

def ActiveSuffix (x : Fin (r + 1 + 1) → ℝ) (q : BlockIndex r) : Prop :=
  ∃ j : Fin r, j.succ.val < r ∧ j.succ ∈ q.2.1 ∧
    SplitValues (blockWordValues x q) j ∧
    blockApexValue x q = blockWordValues x q 0

theorem ActivePrefix.witness_unique {x : Fin (r + 1 + 1) → ℝ} {q : BlockIndex r}
    {j k : Fin r} (hj : SplitValues (blockWordValues x q) j)
    (hk : SplitValues (blockWordValues x q) k) : j = k :=
  hj.unique hk

theorem ActiveSuffix.witness_unique {x : Fin (r + 1 + 1) → ℝ} {q : BlockIndex r}
    {j k : Fin r} (hj : SplitValues (blockWordValues x q) j)
    (hk : SplitValues (blockWordValues x q) k) : j = k :=
  hj.unique hk

theorem activePrefix_not_activeSuffix {x : Fin (r + 1 + 1) → ℝ}
    {q : BlockIndex r} (hp : ActivePrefix x q) : ¬ ActiveSuffix x q := by
  rintro ⟨k, _, _, hk, hak⟩
  obtain ⟨j, _, _, hj, haj⟩ := hp
  have hjk : j = k := hj.unique hk
  subst k
  exact hj.1 (hak.symm.trans haj)

def toggleCut (a : Fin (r + 1)) (S : Finset (Fin (r + 1))) :
    Finset (Fin (r + 1)) :=
  if a ∈ S then S.erase a else insert a S

@[simp] theorem mem_toggleCut_self (a : Fin (r + 1)) (S : Finset (Fin (r + 1))) :
    a ∈ toggleCut a S ↔ a ∉ S := by
  by_cases ha : a ∈ S <;> simp [toggleCut, ha]

theorem mem_toggleCut_of_ne {a b : Fin (r + 1)} {S : Finset (Fin (r + 1))}
    (hba : b ≠ a) : b ∈ toggleCut a S ↔ b ∈ S := by
  by_cases ha : a ∈ S <;> simp [toggleCut, ha, hba]

theorem toggleCut_involutive (a : Fin (r + 1)) :
    Function.Involutive (toggleCut a) := by
  intro S
  by_cases ha : a ∈ S
  · simp [toggleCut, ha]
  · simp [toggleCut, ha]

theorem toggleCut_subset {a : Fin (r + 1)} {S T : Finset (Fin (r + 1))}
    (hS : S ⊆ T) (ha : a ∈ T) : toggleCut a S ⊆ T := by
  intro i hi
  by_cases hia : i = a
  · rwa [hia]
  · exact hS ((mem_toggleCut_of_ne hia).mp hi)

theorem toggleCut_nonempty_of_mem {a b : Fin (r + 1)} {S : Finset (Fin (r + 1))}
    (hb : b ∈ S) (hba : b ≠ a) : (toggleCut a S).Nonempty :=
  ⟨b, (mem_toggleCut_of_ne hba).mpr hb⟩

theorem mem_admissibleCuts_iff {S : Finset (Fin (r + 1))} :
    S ∈ admissibleCuts r ↔ S ⊆ cutPositions r ∧ S ≠ ∅ := by
  simpa [admissibleCuts, and_comm]

theorem mem_cutPositions_iff {i : Fin (r + 1)} :
    i ∈ cutPositions r ↔ i ≠ 0 := by
  simp [cutPositions]

theorem toggleCut_mem_admissible {a b : Fin (r + 1)} {S : Finset (Fin (r + 1))}
    (hS : S ∈ admissibleCuts r) (ha0 : a ≠ 0) (hb : b ∈ S) (hba : b ≠ a) :
    toggleCut a S ∈ admissibleCuts r := by
  rw [mem_admissibleCuts_iff] at hS ⊢
  refine ⟨toggleCut_subset hS.1 ((mem_cutPositions_iff).mpr ha0), ?_⟩
  exact (toggleCut_nonempty_of_mem hb hba).ne_empty

theorem card_toggleCut_of_mem {a : Fin (r + 1)} {S : Finset (Fin (r + 1))}
    (ha : a ∈ S) : (toggleCut a S).card + 1 = S.card := by
  rw [toggleCut, if_pos ha, Finset.card_erase_of_mem ha]
  have hc : 1 ≤ S.card := (Nat.succ_le_iff).mpr (Finset.card_pos.mpr ⟨a, ha⟩)
  exact Nat.sub_add_cancel hc

theorem card_toggleCut_of_not_mem {a : Fin (r + 1)} {S : Finset (Fin (r + 1))}
    (ha : a ∉ S) : (toggleCut a S).card = S.card + 1 := by
  rw [toggleCut, if_neg ha, Finset.card_insert_of_not_mem ha]

theorem wordWeight_toggleCut (a : Fin (r + 1)) (S : Finset (Fin (r + 1))) :
    wordWeight r (toggleCut a S) = -wordWeight r S := by
  unfold wordWeight
  by_cases ha : a ∈ S
  · have hc := card_toggleCut_of_mem ha
    have he : r + 1 + 1 + S.card = (r + 1 + 1 + (toggleCut a S).card) + 1 := by
      omega
    rw [he, pow_succ]
    ring
  · rw [card_toggleCut_of_not_mem ha]
    have he : r + 1 + 1 + (S.card + 1) = (r + 1 + 1 + S.card) + 1 := by omega
    rw [he, pow_succ]
    ring

end MaxNN.Caterpillar
