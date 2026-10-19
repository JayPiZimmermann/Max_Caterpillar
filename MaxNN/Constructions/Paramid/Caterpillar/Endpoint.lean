import MaxNN.Constructions.Paramid.Caterpillar.Words

/-! # Cancellation by moving the last spine endpoint

The final cut can be inserted or removed without changing the pointed base.
The two choices have opposite signs. The theorem below is quantified over
every word length and every evaluation of its vertices; no finite certificate
or geometric cancellation assumption occurs in its statement.
-/

open BigOperators

namespace MaxNN.Caterpillar

theorem alternating_powerset_insert {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) (ha : a ∉ s) (f : Finset α → ℝ)
    (hf : ∀ t ∈ s.powerset, f (insert a t) = f t) :
    ∑ t in (insert a s).powerset, (-1 : ℝ) ^ t.card * f t = 0 := by
  have hnot : ∀ t ∈ s.powerset, a ∉ t := fun t ht =>
    Finset.not_mem_of_mem_powerset_of_not_mem ht ha
  have hd : Disjoint s.powerset (s.powerset.image (insert a)) := by
    apply Finset.disjoint_left.2
    intro t ht hi
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hi
    exact hnot _ ht (Finset.mem_insert_self _ _)
  have hinj : ∀ t ∈ s.powerset, ∀ u ∈ s.powerset, insert a t = insert a u → t = u := by
    intro t ht u hu h
    have he := congrArg (Finset.erase · a) h
    simpa only [Finset.erase_insert (hnot t ht), Finset.erase_insert (hnot u hu)] using he
  rw [Finset.powerset_insert, Finset.sum_union hd, Finset.sum_image hinj,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.card_insert_of_not_mem (hnot t ht), hf t ht, pow_succ]
  ring

/-- Endpoint cancellation for an arbitrary function of the pointed base.
There are at least two vertices (`1 ≤ r`). All block decompositions are
included, including the zero-length spine. -/
theorem endpoint_cancellation (r : ℕ) (hr : 1 ≤ r) (w : Fin (r + 1) → ℝ)
    (F : ℝ → ℝ) :
    ∑ S in (cutPositions r).powerset, (-1 : ℝ) ^ S.card * F (pointedMax w S) = 0 := by
  have hlast : Fin.last r ≠ (0 : Fin (r + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega
  have hmem : Fin.last r ∈ cutPositions r :=
    Finset.mem_erase.2 ⟨hlast, Finset.mem_univ _⟩
  rw [← Finset.insert_erase hmem]
  apply alternating_powerset_insert _ _ (Finset.not_mem_erase _ _)
  intro S _
  rw [pointedMax_insert_last]

/-- The same cancellation after joining the pointed base to any fixed
complementary base and apex. This is the expression needed for block facets. -/
theorem endpoint_join_cancellation (r : ℕ) (hr : 1 ≤ r) (w : Fin (r + 1) → ℝ)
    (apex complement : ℝ) :
    ∑ S in (cutPositions r).powerset,
      (-1 : ℝ) ^ S.card * max apex (pointedMax w S + complement) = 0 :=
  endpoint_cancellation r hr w (fun z => max apex (z + complement))

end MaxNN.Caterpillar
