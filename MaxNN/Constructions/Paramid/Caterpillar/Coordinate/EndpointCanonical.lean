import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Active
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.ReindexCuts

/-! # Canonical endpoint insertion words -/

namespace MaxNN.Caterpillar

variable {s : ℕ}

private theorem finFun_heq_of_cast {α : Type*} {n m : ℕ} (h : n = m)
    (f : Fin n → α) (g : Fin m → α)
    (heq : ∀ i, f i = g (Fin.cast h i)) : HEq f g := by
  subst m
  exact heq_of_eq (funext fun i => heq i)

private theorem finset_heq_of_cast {n m : ℕ} (h : n = m)
    (S : Finset (Fin n)) (T : Finset (Fin m))
    (hmem : ∀ i, i ∈ S ↔ Fin.cast h i ∈ T) : HEq S T := by
  subst m
  apply heq_of_eq
  ext i
  exact hmem i

theorem coordinateUpperUnit_first (π : Equiv.Perm (Fin (s + 2)))
    (S : Finset (Fin (s + 1))) :
    coordinateUpperUnit (1 : Fin (s + 3)) π (firstInsertCuts S) =
      coordinateFirstUnit π S := by
  unfold coordinateUpperUnit coordinateFirstUnit coordinateA
  rw [show (1 : Fin (s + 3)) = (0 : Fin (s + 2)).succ by
      apply Fin.ext
      rfl,
    coordinateUpperWord_succ_apex, coordinateUpperWord_succ_tail]
  funext y
  unfold caterpillarUnit
  congr 1
  congr 1
  · omega
  · apply finFun_heq_of_cast (by omega)
    intro i
    simp only [values]
    refine Fin.cases ?_ (fun q => ?_) i
    · change dot 0 y = dot 0 y
      rfl
    · rw [show Fin.cast _ q.succ = rightPos 0 (Fin.cast (by omega) q) by
          apply Fin.ext; change q.val + 1 = 1 + q.val; omega]
      simp [Fin.insertNth_zero', Fin.append, rightPos]
  · apply finset_heq_of_cast (by omega)
    intro i
    simp only [firstInsertCuts, joinCuts, Finset.image_empty, Finset.empty_union,
      Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (hi | ⟨q, hq, rfl⟩)
      · left
        apply Fin.ext
        simpa [rightPos] using congrArg Fin.val hi
      · right
        refine ⟨q, hq, ?_⟩
        apply Fin.ext
        change 1 + q.val = q.val + 1
        omega
    · rintro (hi | hi)
      · left
        apply Fin.ext
        simpa [rightPos] using congrArg Fin.val hi
      · rcases hi with ⟨q, hq, hqi⟩
        right
        refine ⟨q, hq, ?_⟩
        apply Fin.ext
        have hv := congrArg Fin.val hqi
        change 1 + q.val = i.val at hv
        change q.val + 1 = i.val
        omega

end MaxNN.Caterpillar
