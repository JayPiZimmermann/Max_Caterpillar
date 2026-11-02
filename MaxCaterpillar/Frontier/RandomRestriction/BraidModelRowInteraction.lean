import MaxCaterpillar.Frontier.RandomRestriction.BraidModelRow

/-! # Exact signed interaction of an actual braid row

The symmetrized quadratic entry is determined by the actual unordered row
support and actual coordinate magnitude, independently of its chosen braid
orientation. Zero rows are included.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.BraidModel.BraidPair
variable {row : Point 5}

theorem apply_left (p : BraidPair row) : row p.left = p.scale := by
  have h := congrArg (fun c : Point 5 => c p.left) p.row_eq
  simpa [Pi.smul_apply, unitVec, p.distinct] using h

theorem apply_right (p : BraidPair row) : row p.right = -p.scale := by
  have h := congrArg (fun c : Point 5 => c p.right) p.row_eq
  simpa [Pi.smul_apply, unitVec, p.distinct.symm] using h

theorem abs_left (p : BraidPair row) : |row p.left| = |p.scale| := by
  rw [p.apply_left]

theorem abs_right (p : BraidPair row) : |row p.right| = |p.scale| := by
  rw [p.apply_right, abs_neg]

theorem rowSupport_eq_pair_of_scale_ne_zero (p : BraidPair row) (ht : p.scale ≠ 0) :
    NormalizedNetwork.rowSupport row = {p.left, p.right} := by
  classical
  ext i
  simp only [NormalizedNetwork.mem_rowSupport, Finset.mem_insert, Finset.mem_singleton]
  have hi := congrArg (fun c : Point 5 => c i) p.row_eq
  change row i = p.scale *
    ((if i = p.left then 1 else 0) - (if i = p.right then 1 else 0)) at hi
  rw [hi]
  by_cases hl : i = p.left
  · subst i
    simp [p.distinct, ht]
  · by_cases hr : i = p.right
    · subst i
      simp [p.distinct.symm, ht]
    · simp [hl, hr]

theorem quadraticCoeff_symm_eq_rowSupport (p : BraidPair row) (a b : Fin 5)
    (hab : a ≠ b) :
    p.quadraticCoeff a b + p.quadraticCoeff b a =
      if NormalizedNetwork.rowSupport row = {a, b} then -|row a| else 0 := by
  classical
  by_cases ht : p.scale = 0
  · have hz : row = 0 := p.row_eq.trans (by simp [ht])
    have hs : NormalizedNetwork.rowSupport row = ∅ := by
      rw [hz]
      simp [NormalizedNetwork.rowSupport]
    have hp : (∅ : Finset (Fin 5)) ≠ {a, b} := by
      intro he
      have ha : a ∈ (∅ : Finset (Fin 5)) := by rw [he]; simp
      exact Finset.not_mem_empty a ha
    simp [quadraticCoeff, ht, hs, hp]
  rw [p.rowSupport_eq_pair_of_scale_ne_zero ht]
  by_cases hp : ({p.left, p.right} : Finset (Fin 5)) = {a, b}
  · rw [if_pos hp]
    have hset : ({p.left, p.right} : Set (Fin 5)) = {a, b} := by
      simpa only [Finset.coe_pair] using
        congrArg (fun s : Finset (Fin 5) => (s : Set (Fin 5))) hp
    rcases Set.pair_eq_pair_iff.mp hset with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · subst a
      subst b
      simp [quadraticCoeff, p.distinct, p.distinct.symm, p.abs_left]
    · subst b
      subst a
      simp [quadraticCoeff, p.distinct, p.distinct.symm, p.abs_right]
  · have hdir : ¬(a = p.left ∧ b = p.right) := by
      rintro ⟨rfl, rfl⟩
      exact hp rfl
    have hrev : ¬(b = p.left ∧ a = p.right) := by
      rintro ⟨rfl, rfl⟩
      exact hp (Finset.pair_comm _ _)
    simp [quadraticCoeff, hdir, hrev, hp]

end MaxCaterpillar.Frontier.RandomRestriction.BraidModel.BraidPair
