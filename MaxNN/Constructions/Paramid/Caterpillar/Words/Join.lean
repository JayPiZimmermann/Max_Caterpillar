import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing
import Mathlib.Data.Fin.Tuple.Basic

/-! # Joining two ordered caterpillar words at a spine edge

The boundary between the words is inserted as a spine cut. All parent and
endpoint identities below refer to the original `parent` and `lastHead`
definitions, rather than postulating how the joined tree behaves.
-/

open BigOperators

namespace MaxNN.Caterpillar

variable {r s : ℕ}

def leftPos (s : ℕ) (i : Fin (r + 1)) : Fin (r + 1 + s + 1) := Fin.castAdd (s + 1) i

def rightPos (r : ℕ) (i : Fin (s + 1)) : Fin (r + 1 + s + 1) := Fin.natAdd (r + 1) i

def joinCuts (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) :
    Finset (Fin (r + 1 + s + 1)) :=
  S.image (leftPos s) ∪ insert (rightPos r 0) (T.image (rightPos r))

private theorem parent_eq_of_bounds {S : Finset (Fin (r + 1))}
    {j p : Fin (r + 1)} (hj : 0 < j) (hp : p ∈ insert 0 S) (hpj : p < j)
    (hmax : ∀ q ∈ S, q < j → q ≤ p) : parent S j = p := by
  apply le_antisymm
  · rcases Finset.mem_insert.mp (parent_mem_insert S j) with h0 | hS
    · rw [h0]
      exact Fin.zero_le _
    · exact hmax _ hS (parent_lt hj)
  · rcases Finset.mem_insert.mp hp with h0 | hS
    · rw [h0]
      exact Fin.zero_le _
    · exact le_parent_of_mem hS hpj

private theorem lastHead_eq_of_bounds {S : Finset (Fin (r + 1))}
    {p : Fin (r + 1)} (hp : p ∈ insert 0 S) (hmax : ∀ q ∈ S, q ≤ p) : lastHead S = p := by
  apply le_antisymm
  · have hm := Finset.max'_mem (insert 0 S) (Finset.insert_nonempty _ _)
    change lastHead S ∈ insert 0 S at hm
    rcases Finset.mem_insert.mp hm with h0 | hS
    · rw [h0]
      exact Fin.zero_le _
    · exact hmax _ hS
  · exact Finset.le_max' _ p hp

private theorem left_lt_right (i : Fin (r + 1)) (j : Fin (s + 1)) :
    leftPos s i < rightPos r j := by
  change i.val < r + 1 + j.val
  exact lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)

theorem joinCuts_nonempty (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) :
    (joinCuts S T).Nonempty :=
  ⟨rightPos r 0, Finset.mem_union_right _ (Finset.mem_insert_self _ _)⟩

theorem card_joinCuts (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1)))
    (hT : (0 : Fin (s + 1)) ∉ T) : (joinCuts S T).card = S.card + T.card + 1 := by
  have hl : Function.Injective (leftPos (r := r) s) := by
    intro i j he
    apply Fin.ext
    exact congrArg (fun q : Fin (r + 1 + s + 1) => q.val) he
  have hr : Function.Injective (rightPos (s := s) r) := by
    intro i j he
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg (fun q : Fin (r + 1 + s + 1) => q.val) he)
  have h0 : rightPos r 0 ∉ T.image (rightPos r) := by
    intro hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    exact hT (hr he ▸ hi)
  have hd : Disjoint (S.image (leftPos s)) (insert (rightPos r 0) (T.image (rightPos r))) := by
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
    rcases Finset.mem_insert.mp hq' with hq' | hq'
    · exact (ne_of_lt (left_lt_right a 0)) hq'
    · obtain ⟨b, _, he⟩ := Finset.mem_image.mp hq'
      exact (ne_of_lt (left_lt_right a b)) he.symm
  rw [joinCuts, Finset.card_union_eq hd, Finset.card_insert_of_not_mem h0,
    Finset.card_image_of_injective _ hl, Finset.card_image_of_injective _ hr]
  exact (Nat.add_assoc _ _ _).symm

theorem parent_join_left (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1)))
    (i : Fin (r + 1)) (hi : 0 < i) :
    parent (joinCuts S T) (leftPos s i) = leftPos s (parent S i) := by
  apply parent_eq_of_bounds (by exact hi)
  · rcases Finset.mem_insert.mp (parent_mem_insert S i) with h0 | hS
    · apply Finset.mem_insert.mpr
      left
      rw [h0]
      rfl
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hS, rfl⟩)
  · exact parent_lt hi
  · intro q hq hqi
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact le_parent_of_mem ha hqi
    · rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        exact False.elim ((not_lt_of_gt (left_lt_right i 0)) hqi)
      · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
        exact False.elim ((not_lt_of_gt (left_lt_right i b)) hqi)

theorem parent_join_boundary (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) :
    parent (joinCuts S T) (rightPos r 0) = leftPos s (lastHead S) := by
  apply parent_eq_of_bounds
  · change 0 < r + 1 + 0
    omega
  · have hm := Finset.max'_mem (insert 0 S) (Finset.insert_nonempty _ _)
    change lastHead S ∈ insert 0 S at hm
    rcases Finset.mem_insert.mp hm with h0 | hS
    · apply Finset.mem_insert.mpr
      left
      rw [h0]
      rfl
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hS, rfl⟩)
  · exact left_lt_right _ _
  · intro q hq hqi
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.le_max' _ a (Finset.mem_insert_of_mem ha)
    · rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        exact False.elim ((lt_irrefl _) hqi)
      · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
        have hn : r + 1 + b.val < r + 1 + 0 := hqi
        omega

theorem parent_join_right (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1)))
    (i : Fin (s + 1)) (hi : 0 < i) :
    parent (joinCuts S T) (rightPos r i) = rightPos r (parent T i) := by
  apply parent_eq_of_bounds
  · change 0 < r + 1 + i.val
    omega
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    rcases Finset.mem_insert.mp (parent_mem_insert T i) with h0 | hT
    · rw [h0]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, hT, rfl⟩)
  · change r + 1 + (parent T i).val < r + 1 + i.val
    exact Nat.add_lt_add_left (parent_lt hi) _
  · intro q hq hqi
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
      exact (left_lt_right _ _).le
    · rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        change r + 1 + 0 ≤ r + 1 + (parent T i).val
        exact Nat.add_le_add_left (Nat.zero_le _) _
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
        have hbi : b < i := Nat.lt_of_add_lt_add_left hqi
        change r + 1 + b.val ≤ r + 1 + (parent T i).val
        exact Nat.add_le_add_left (le_parent_of_mem hb hbi) _

theorem lastHead_join (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) :
    lastHead (joinCuts S T) = rightPos r (lastHead T) := by
  apply lastHead_eq_of_bounds
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    have hm := Finset.max'_mem (insert 0 T) (Finset.insert_nonempty _ _)
    change lastHead T ∈ insert 0 T at hm
    rcases Finset.mem_insert.mp hm with h0 | hT
    · rw [h0]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, hT, rfl⟩)
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
      exact (left_lt_right _ _).le
    · rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        change r + 1 + 0 ≤ r + 1 + (lastHead T).val
        exact Nat.add_le_add_left (Nat.zero_le _) _
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
        change r + 1 + b.val ≤ r + 1 + (lastHead T).val
        exact Nat.add_le_add_left (Finset.le_max' _ b (Finset.mem_insert_of_mem hb)) _

theorem parent_zero (S : Finset (Fin (r + 1))) : parent S 0 = 0 := by
  have hf : S.filter (fun i => i < 0) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
    exact fun _ => not_lt.mpr (Fin.zero_le i)
  simp [parent, hf]

theorem parent_join_left_all (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1)))
    (i : Fin (r + 1)) : parent (joinCuts S T) (leftPos s i) = leftPos s (parent S i) := by
  by_cases hi : i = 0
  · subst i
    change parent (joinCuts S T) 0 = leftPos s (parent S 0)
    rw [parent_zero, parent_zero]
    rfl
  · exact parent_join_left S T i (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hi))

private theorem treeMax_eq_sum_all_sub_root (w : Fin (r + 1) → ℝ)
    (S : Finset (Fin (r + 1))) :
    treeMax w S = (∑ i : Fin (r + 1), max (w (parent S i)) (w i)) - w 0 := by
  rw [Fin.sum_univ_succ, parent_zero, max_self]
  unfold treeMax
  ring

theorem treeMax_join (A : Fin (r + 1) → ℝ) (B : Fin (s + 1) → ℝ)
    (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) :
    treeMax (r := r + 1 + s) (Fin.append (m := r + 1) (n := s + 1) A B) (joinCuts S T) =
      treeMax A S + treeMax B T + max (A (lastHead S)) (B 0) := by
  have hl : (∑ i : Fin (r + 1), max
      (Fin.append A B (parent (joinCuts S T) (leftPos s i)))
      (Fin.append A B (leftPos s i))) = A 0 + treeMax A S := by
    calc
      _ = ∑ i : Fin (r + 1), max (A (parent S i)) (A i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [parent_join_left_all S T i]
        simp only [leftPos, Fin.append_left]
      _ = A 0 + treeMax A S := by
        rw [Fin.sum_univ_succ, parent_zero, max_self]
        rfl
  have hr : (∑ i : Fin (s + 1), max
      (Fin.append A B (parent (joinCuts S T) (rightPos r i)))
      (Fin.append A B (rightPos r i))) = max (A (lastHead S)) (B 0) + treeMax B T := by
    rw [Fin.sum_univ_succ, parent_join_boundary]
    have he : ∀ j : Fin s, max
        (Fin.append A B (parent (joinCuts S T) (rightPos r j.succ)))
        (Fin.append A B (rightPos r j.succ)) = max (B (parent T j.succ)) (B j.succ) := by
      intro j
      rw [parent_join_right S T j.succ (Fin.succ_pos j)]
      simp only [rightPos, Fin.append_right]
    simp_rw [he]
    simp only [leftPos, rightPos, Fin.append_left, Fin.append_right, treeMax]
  rw [treeMax_eq_sum_all_sub_root]
  have hsplit := Fin.sum_univ_add (a := r + 1) (b := s + 1)
    (fun i : Fin ((r + 1) + (s + 1)) =>
      max (Fin.append A B (parent (joinCuts S T) i)) (Fin.append A B i))
  refine (congrArg (fun z : ℝ => z - Fin.append A B (leftPos s 0)) hsplit).trans ?_
  change (∑ i : Fin (r + 1), max
      (Fin.append A B (parent (joinCuts S T) (leftPos s i))) (Fin.append A B (leftPos s i))) +
    (∑ i : Fin (s + 1), max
      (Fin.append A B (parent (joinCuts S T) (rightPos r i))) (Fin.append A B (rightPos r i))) -
    Fin.append A B (leftPos s 0) = _
  rw [hl, hr]
  simp only [leftPos, Fin.append_left]
  ring

/-- The exact base identity needed to apply the endpoint-fibre theorem to a
word split at a spine cut. It is valid for every pair of word lengths. -/
theorem baseMax_join (A : Fin (r + 1) → ℝ) (B : Fin (s + 1) → ℝ)
    (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) :
    baseMax (r := r + 1 + s) (Fin.append (m := r + 1) (n := s + 1) A B) (joinCuts S T) =
      pointedMax A S + baseMax B T + max (A (lastHead S)) (B 0) - B 0 := by
  unfold baseMax pointedMax
  rw [treeMax_join A B S T, lastHead_join S T]
  have hsum : (∑ i : Fin (r + 1 + s + 1), Fin.append A B i) =
      (∑ i : Fin (r + 1), A i) + ∑ i : Fin (s + 1), B i := by
    simpa only [Fin.append_left, Fin.append_right] using
      Fin.sum_univ_add (a := r + 1) (b := s + 1)
        (Fin.append (m := r + 1) (n := s + 1) A B)
  rw [hsum]
  change _ + Fin.append A B (leftPos s 0) + Fin.append A B (rightPos r (lastHead T)) = _
  simp only [leftPos, rightPos, Fin.append_left, Fin.append_right]
  ring

end MaxNN.Caterpillar
