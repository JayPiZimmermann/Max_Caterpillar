import MaxNN.Constructions.Paramid.Caterpillar.Words

/-! Translation of every vertex value adds the same constant to the base. -/

open BigOperators

namespace MaxNN.Caterpillar

variable {r : ℕ}

theorem pointedMax_add_const (w : Fin (r + 1) → ℝ) (c : ℝ)
    (S : Finset (Fin (r + 1))) : pointedMax (fun i => w i + c) S = pointedMax w S := by
  unfold pointedMax treeMax
  simp only [max_add_add_right, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem baseMax_add_const (w : Fin (r + 1) → ℝ) (c : ℝ)
    (S : Finset (Fin (r + 1))) : baseMax (fun i => w i + c) S = baseMax w S + c := by
  rw [baseMax, pointedMax_add_const, baseMax]
  ring

end MaxNN.Caterpillar
