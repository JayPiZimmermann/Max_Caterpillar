import MaxNN.Constructions.Paramid.Caterpillar.Formula.Simplex

/-! # Repeated levels in full simplex coordinates

A noncoordinate two-level direction has no singleton value class. The proofs
below extract the precise base-word hypotheses needed for every apex choice.
-/

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

def RepeatedValues {ι : Type*} (x : ι → ℝ) : Prop :=
  ∀ a, ∃ b, b ≠ a ∧ x b = x a

theorem repeatedValues_base_has_apex (x : Fin (r + 1 + 1) → ℝ)
    (hx : RepeatedValues x) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    ∃ i : Fin (r + 1), x (π i.succ) = x (π 0) := by
  obtain ⟨b, hb, hv⟩ := hx (π 0)
  obtain ⟨q, rfl⟩ := π.surjective b
  rcases Fin.eq_zero_or_eq_succ q with h0 | ⟨i, hi⟩
  · exact False.elim (hb (congrArg π h0))
  · exact ⟨i, hi ▸ hv⟩

theorem repeatedValues_base_other_repeated (x : Fin (r + 1 + 1) → ℝ)
    (hx : RepeatedValues x) (π : Equiv.Perm (Fin (r + 1 + 1)))
    (i : Fin (r + 1)) (hi : x (π i.succ) ≠ x (π 0)) :
    ∃ k : Fin (r + 1), k ≠ i ∧ x (π k.succ) = x (π i.succ) := by
  obtain ⟨b, hb, hv⟩ := hx (π i.succ)
  obtain ⟨q, rfl⟩ := π.surjective b
  rcases Fin.eq_zero_or_eq_succ q with h0 | ⟨k, hk⟩
  · rw [h0] at hv
    exact False.elim (hi hv.symm)
  · refine ⟨k, ?_, hk ▸ hv⟩
    intro he
    apply hb
    rw [hk, he]

theorem simplex_base_has_other (u : Fin (r + 1) → ℝ) (hu : u ≠ 0)
    (π : Equiv.Perm (Fin (r + 1 + 1))) :
    ∃ i : Fin (r + 1), simplexValues u (π i.succ) ≠ simplexValues u (π 0) := by
  classical
  by_contra hn
  have hb : ∀ i : Fin (r + 1), simplexValues u (π i.succ) = simplexValues u (π 0) := by
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  have hfull : ∀ a, simplexValues u a = simplexValues u (π 0) := by
    intro a
    obtain ⟨q, rfl⟩ := π.surjective a
    refine Fin.cases rfl (fun i => hb i) q
  have hzero := hfull 0
  rw [simplexValues_zero] at hzero
  apply hu
  funext i
  have hi := hfull i.succ
  rw [simplexValues_succ, ← hzero] at hi
  exact hi

end MaxNN.Caterpillar
