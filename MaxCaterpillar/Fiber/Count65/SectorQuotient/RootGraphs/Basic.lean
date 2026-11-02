import MaxCaterpillar.Fiber.Count65.Star.Stabilizer
import MaxCaterpillar.Frontier.Basic
import Mathlib.Tactic.Linarith

/-! # Directed roots of actual first hidden layer rows -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient
open MaxCaterpillar.Frontier

/-- A positive multiple of the directed root e_a-e_b, stated in coordinates. -/
def IsDirectedRootRow (u : Point 4) (a b : Fin 4) : Prop :=
  a ≠ b ∧ 0 < u a ∧ u a + u b = 0 ∧ ∀ i, i ≠ a → i ≠ b → u i = 0

/-- The oriented root graph present among the actual first hidden layer rows. -/
def directedRootGraph (A : Fin 6 → Point 4) (a b : Fin 4) : Prop :=
  ∃ j, IsDirectedRootRow (A j) a b

lemma isDirectedRootRow_pos_mul (u : Point 4) (a b : Fin 4)
    (s : ℝ) (hs : 0 < s) :
    IsDirectedRootRow (fun i => s * u i) a b ↔ IsDirectedRootRow u a b := by
  constructor
  · rintro ⟨hne,hpos,hsum,hzero⟩
    refine ⟨hne,?_,?_,?_⟩
    · exact pos_of_mul_pos_right hpos (le_of_lt hs)
    · have he : s * (u a + u b) = 0 := by rw [mul_add]; exact hsum
      exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hs)
    · intro i hia hib
      exact (mul_eq_zero.mp (hzero i hia hib)).resolve_left (ne_of_gt hs)
  · rintro ⟨hne,hpos,hsum,hzero⟩
    refine ⟨hne,mul_pos hs hpos,?_,?_⟩
    · rw [← mul_add,hsum,mul_zero]
    · intro i hia hib
      change s * u i = 0
      rw [hzero i hia hib,mul_zero]

lemma isDirectedRootRow_input_perm (u : Point 4) (q : Equiv.Perm (Fin 4))
    (a b : Fin 4) :
    IsDirectedRootRow (fun i => u (q i)) a b ↔ IsDirectedRootRow u (q a) (q b) := by
  constructor
  · rintro ⟨hne,hpos,hsum,hzero⟩
    refine ⟨fun h => hne (q.injective h),hpos,hsum,?_⟩
    intro i hia hib
    have ha : q.symm i ≠ a := by
      intro h
      apply hia
      calc i = q (q.symm i) := (q.apply_symm_apply i).symm
           _ = q a := congrArg q h
    have hb : q.symm i ≠ b := by
      intro h
      apply hib
      calc i = q (q.symm i) := (q.apply_symm_apply i).symm
           _ = q b := congrArg q h
    simpa only [q.apply_symm_apply] using hzero (q.symm i) ha hb
  · rintro ⟨hne,hpos,hsum,hzero⟩
    refine ⟨fun h => hne (congrArg q h),hpos,hsum,?_⟩
    intro i hia hib
    exact hzero (q i) (fun h => hia (q.injective h)) (fun h => hib (q.injective h))

/-- Positive row rescaling and hidden/input permutations preserve directed roots. -/
theorem directedRootGraph_relabel (A B : Fin 6 → Point 4)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (h : ∀ j i, B j i = s j * A (p j) (q i)) (a b : Fin 4) :
    directedRootGraph B a b ↔ directedRootGraph A (q a) (q b) := by
  have row (j : Fin 6) :
      IsDirectedRootRow (B j) a b ↔ IsDirectedRootRow (A (p j)) (q a) (q b) := by
    have he : B j = fun i => s j * A (p j) (q i) := funext (h j)
    rw [he,isDirectedRootRow_pos_mul _ _ _ _ (hs j),isDirectedRootRow_input_perm]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨p j,(row j).mp hj⟩
  · rintro ⟨j,hj⟩
    refine ⟨p.symm j,(row (p.symm j)).mpr ?_⟩
    simpa only [p.apply_symm_apply] using hj

end MaxCaterpillar.Fiber.Count65.SectorQuotient
