import MaxNN.Constructions.Paramid.Caterpillar.Words

/-! # A unique crossing edge in an ordered caterpillar

The parent relation is connected to position zero. If vertex values change
across only one edge, that edge either isolates one pendant vertex, or is a
spine cut separating a constant prefix from a constant suffix.

These statements concern arbitrary word lengths and arbitrary vertex values.
They are the combinatorial classification needed before reindexing the global
block-facet sum into the endpoint fibres. No global sum identity is asserted.
-/

open BigOperators

namespace MaxNN.Caterpillar

variable {r : ℕ} {α : Type*}

theorem parent_mem_insert (S : Finset (Fin (r + 1))) (j : Fin (r + 1)) :
    parent S j ∈ insert 0 S := by
  have h := Finset.max'_mem (insert 0 (S.filter fun i => i < j)) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp h with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mp h).1)

theorem le_parent_of_mem {S : Finset (Fin (r + 1))} {i j : Fin (r + 1)}
    (hi : i ∈ S) (hij : i < j) : i ≤ parent S j := by
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hi, hij⟩)

theorem parent_ne_pendant (S : Finset (Fin (r + 1))) (j : Fin r)
    (hj : j.succ ∉ S) (i : Fin (r + 1)) : parent S i ≠ j.succ := by
  intro he
  have hm := parent_mem_insert S i
  rw [he] at hm
  rcases Finset.mem_insert.mp hm with h0 | hS
  · exact Fin.succ_ne_zero j h0
  · exact hj hS

theorem lastHead_ne_pendant (S : Finset (Fin (r + 1))) (j : Fin r)
    (hj : j.succ ∉ S) : lastHead S ≠ j.succ := by
  intro he
  have hm := Finset.max'_mem (insert 0 S) (Finset.insert_nonempty _ _)
  change lastHead S ∈ insert 0 S at hm
  rw [he] at hm
  rcases Finset.mem_insert.mp hm with h0 | hS
  · exact Fin.succ_ne_zero j h0
  · exact hj hS

/-- Values are determined by their root value and implications along parent
edges. The least disagreement would have a still smaller disagreement. -/
theorem word_eq_of_root_and_parent_imp (S : Finset (Fin (r + 1)))
    (w v : Fin (r + 1) → α) (h0 : w 0 = v 0)
    (hstep : ∀ k : Fin r,
      w (parent S k.succ) = v (parent S k.succ) → w k.succ = v k.succ) : w = v := by
  classical
  by_contra hne
  let bad := Finset.univ.filter fun i => w i ≠ v i
  have hbad : bad.Nonempty := by
    by_contra he
    apply hne
    funext i
    by_contra hi
    exact he ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let j := bad.min' hbad
  have hj : w j ≠ v j := (Finset.mem_filter.mp (Finset.min'_mem bad hbad)).2
  rcases Fin.eq_zero_or_eq_succ j with hj0 | ⟨k, hk⟩
  · exact hj (by rw [hj0]; exact h0)
  · have hkbad : w k.succ ≠ v k.succ := by rwa [hk] at hj
    have hpbad : w (parent S k.succ) ≠ v (parent S k.succ) :=
      fun h => hkbad (hstep k h)
    have hmin : j ≤ parent S k.succ :=
      Finset.min'_le bad _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpbad⟩)
    rw [hk] at hmin
    exact not_le_of_gt (parent_lt (Fin.succ_pos k)) hmin

/-- A nonconstant assignment has a crossing parent edge. This rules out the
zero-crossing case for a nonempty proper block of vertices. -/
theorem exists_parent_value_ne (S : Finset (Fin (r + 1))) (w : Fin (r + 1) → α)
    {i : Fin (r + 1)} (hi : w i ≠ w 0) :
    ∃ k : Fin r, w k.succ ≠ w (parent S k.succ) := by
  classical
  by_contra h
  have he : ∀ k : Fin r, w k.succ = w (parent S k.succ) := by
    intro k
    by_contra hk
    exact h ⟨k, hk⟩
  have hall := word_eq_of_root_and_parent_imp S w (fun _ => w 0) rfl
    (fun k hk => (he k).trans hk)
  exact hi (congrFun hall i)

/-- If the only possible crossing is not a spine cut, every other vertex has
the root value. Thus the exceptional side consists of one pendant vertex. -/
theorem unique_edge_not_cut_values (S : Finset (Fin (r + 1)))
    (w : Fin (r + 1) → α) (j : Fin r) (hj : j.succ ∉ S)
    (hother : ∀ k : Fin r, k ≠ j → w k.succ = w (parent S k.succ)) :
    ∀ i : Fin (r + 1), i ≠ j.succ → w i = w 0 := by
  have hp : ∀ k : Fin r, parent S k.succ ≠ j.succ :=
    fun k => parent_ne_pendant S j hj k.succ
  let v : Fin (r + 1) → α := fun i => if i = j.succ then w j.succ else w 0
  have hall : w = v := by
    apply word_eq_of_root_and_parent_imp S w v
    · change w 0 = if (0 : Fin (r + 1)) = j.succ then w j.succ else w 0
      rw [if_neg (Fin.succ_ne_zero j).symm]
    · intro k hk
      by_cases hkj : k = j
      · subst k
        change w j.succ = if j.succ = j.succ then w j.succ else w 0
        rw [if_pos rfl]
      · have hks : k.succ ≠ j.succ := fun he => hkj (Fin.succ_injective r he)
        change w (parent S k.succ) =
          (if parent S k.succ = j.succ then w j.succ else w 0) at hk
        rw [if_neg (hp k)] at hk
        change w k.succ = if k.succ = j.succ then w j.succ else w 0
        rw [if_neg hks]
        exact (hother k hkj).trans hk
  intro i hi
  have h := congrFun hall i
  change w i = if i = j.succ then w j.succ else w 0 at h
  rwa [if_neg hi] at h

/-- If the only possible crossing is a spine cut, the word is constant on
each of its two consecutive sides. The exceptional edge may also have equal
endpoint values; no artificial nondegeneracy hypothesis is needed. -/
theorem unique_edge_cut_values (S : Finset (Fin (r + 1)))
    (w : Fin (r + 1) → α) (j : Fin r) (hj : j.succ ∈ S)
    (hother : ∀ k : Fin r, k ≠ j → w k.succ = w (parent S k.succ)) :
    ∀ i : Fin (r + 1), w i = if i < j.succ then w 0 else w j.succ := by
  let v : Fin (r + 1) → α := fun i => if i < j.succ then w 0 else w j.succ
  have hall : w = v := by
    apply word_eq_of_root_and_parent_imp S w v
    · change w 0 = if (0 : Fin (r + 1)) < j.succ then w 0 else w j.succ
      rw [if_pos (Fin.succ_pos j)]
    · intro k hk
      by_cases hkj : k = j
      · subst k
        change w j.succ = if j.succ < j.succ then w 0 else w j.succ
        rw [if_neg (lt_irrefl _)]
      · have hv : v (parent S k.succ) = v k.succ := by
          by_cases hlt : k.succ < j.succ
          · have hplt := lt_trans (parent_lt (S := S) (Fin.succ_pos k)) hlt
            simp only [v, if_pos hplt, if_pos hlt]
          · have hjs : j.succ < k.succ := lt_of_le_of_ne (not_lt.mp hlt)
              (fun he => hkj (Fin.succ_injective r he.symm))
            have hpj := le_parent_of_mem hj hjs
            simp only [v, if_neg hlt, if_neg (not_lt.mpr hpj)]
        exact (hother k hkj).trans (hk.trans hv)
  exact fun i => congrFun hall i

theorem baseMax_eq_sum_parent_diff (w : Fin (r + 1) → ℝ)
    (S : Finset (Fin (r + 1))) :
    baseMax w S = (∑ j : Fin r, (max (w (parent S j.succ)) (w j.succ) - w j.succ)) +
      w (lastHead S) := by
  unfold baseMax pointedMax treeMax
  rw [Fin.sum_univ_succ w, Finset.sum_sub_distrib]
  ring

/-- A pendant with a different value affects just its incident edge. This
closed evaluation will separate the pendant case from spine-cut cancellation. -/
theorem baseMax_single_pendant (w : Fin (r + 1) → ℝ)
    (S : Finset (Fin (r + 1))) (j : Fin r) (hj : j.succ ∉ S) (c : ℝ)
    (hw : ∀ i : Fin (r + 1), i ≠ j.succ → w i = c) :
    baseMax w S = max c (w j.succ) + c - w j.succ := by
  rw [baseMax_eq_sum_parent_diff]
  have hs : (∑ k : Fin r, (max (w (parent S k.succ)) (w k.succ) - w k.succ)) =
      max c (w j.succ) - w j.succ := by
    rw [Finset.sum_eq_single j]
    · rw [hw _ (parent_ne_pendant S j hj _)]
    · intro k _ hkj
      rw [hw _ (parent_ne_pendant S j hj _),
        hw _ (fun he => hkj (Fin.succ_injective r he)), max_self, sub_self]
    · intro h
      exact False.elim (h (Finset.mem_univ j))
  rw [hs, hw _ (lastHead_ne_pendant S j hj)]
  ring

end MaxNN.Caterpillar
