import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Permutations
import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Paramid
import MaxNN.Constructions.Paramid.Caterpillar.Words.SwapFirst

/-! # Lower-dimensional coordinate terms outside the insertion fibres

For the all-ones coordinate normal, insertion of the distinguished vertex
at an unpaired word position leaves either a strict outer maximum or at least
two crossing tree edges.  These are precisely the local estimates used to
discard the terms outside pendant and endpoint insertion fibres.
-/

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

theorem dot_insertZeroPerm_at (p : Fin (r + 1 + 1))
    (τ : Equiv.Perm (Fin (r + 1))) :
    dot (toR (vtx (insertZeroPerm p τ p))) (zeroCoordinateDirection (r + 1)) = 0 := by
  change simplexValues (zeroCoordinateDirection (r + 1)) (insertZeroPerm p τ p) = 0
  rw [insertZeroPerm_at, simplexValues_zeroCoordinateDirection_zero]

theorem dot_insertZeroPerm_of_ne (p q : Fin (r + 1 + 1))
    (τ : Equiv.Perm (Fin (r + 1))) (hqp : q ≠ p) :
    dot (toR (vtx (insertZeroPerm p τ q))) (zeroCoordinateDirection (r + 1)) = 1 := by
  have hz : insertZeroPerm p τ q ≠ 0 := by
    intro hzero
    apply hqp
    apply (insertZeroPerm p τ).injective
    rw [hzero, insertZeroPerm_at]
  obtain ⟨i, hi⟩ := (Fin.eq_zero_or_eq_succ (insertZeroPerm p τ q)).resolve_left hz
  change simplexValues (zeroCoordinateDirection (r + 1)) (insertZeroPerm p τ q) = 1
  rw [hi, simplexValues_zeroCoordinateDirection_succ]

/-- If the distinguished vertex is the apex, both outer maxima are strict. -/
theorem germDiff_insertZeroPerm_zero_mem_LSpan_one
    (τ : Equiv.Perm (Fin (r + 1))) (S : Finset (Fin (r + 1))) :
    germDiff (zeroCoordinateDirection (r + 1))
      (caterpillarUnit (toR (vtx ((insertZeroPerm 0 τ) 0)))
        (fun i => toR (vtx ((insertZeroPerm 0 τ) i.succ))) S) ∈
      LSpan (r + 1) 1 := by
  let π := insertZeroPerm (0 : Fin (r + 1 + 1)) τ
  let u := zeroCoordinateDirection (r + 1)
  let A : Fin (r + 1) → Fin (r + 1) → ℝ := fun i => toR (vtx (π i.succ))
  have hapex : dot (toR (vtx (π 0))) u = 0 :=
    dot_insertZeroPerm_at (0 : Fin (r + 1 + 1)) τ
  have hA : ∀ i, dot (A i) u = 1 := by
    intro i
    exact dot_insertZeroPerm_of_ne 0 i.succ τ (Fin.succ_ne_zero i)
  have hbase : baseMax (values A u) S = 1 :=
    baseMax_of_constant _ S 1 hA
  have hAneg : ∀ i, dot (A i) (-u) = -1 := by
    intro i
    rw [UnitGermAux.dot_neg_right, hA]
  have hbaseNeg : baseMax (values A (-u)) S = -1 :=
    baseMax_of_constant _ S (-1) hAneg
  have hp := germ_caterpillarUnit_mem_LSpan_one_of_ne (toR (vtx (π 0))) A S u (by
    rw [hapex, hbase]
    norm_num)
  have hn := germ_caterpillarUnit_mem_LSpan_one_of_ne (toR (vtx (π 0))) A S (-u) (by
    rw [UnitGermAux.dot_neg_right, hapex, hbaseNeg]
    norm_num)
  exact Submodule.sub_mem _ hp hn

/-- If the distinguished vertex is the base root and the first cut is absent,
the first two base edges both cross the coordinate normal. -/
theorem germDiff_insertZeroPerm_one_mem_LSpan (hr : 2 ≤ r)
    (τ : Equiv.Perm (Fin (r + 1))) (S : Finset (Fin (r + 1)))
    (h1 : (1 : Fin (r + 1)) ∉ S) :
    germDiff (zeroCoordinateDirection (r + 1))
      (caterpillarUnit (toR (vtx ((insertZeroPerm 1 τ) 0)))
        (fun i => toR (vtx ((insertZeroPerm 1 τ) i.succ))) S) ∈
      LSpan (r + 1) (r - 1) := by
  let π := insertZeroPerm (1 : Fin (r + 1 + 1)) τ
  let u := zeroCoordinateDirection (r + 1)
  let A : Fin (r + 1) → Fin (r + 1) → ℝ := fun i => toR (vtx (π i.succ))
  let j : Fin r := ⟨0, by omega⟩
  let k : Fin r := ⟨1, by omega⟩
  have hjk : j ≠ k := by
    intro h
    have := congrArg Fin.val h
    simp only [j, k] at this
  have hjchild : j.succ = (1 : Fin (r + 1)) := by
    apply Fin.ext
    change 1 = 1 % (r + 1)
    rw [Nat.mod_eq_of_lt]
    omega
  have hjparent : parent S j.succ = 0 := by
    have hlt := parent_lt (S := S) (Fin.succ_pos j)
    apply Fin.ext
    change (parent S j.succ).val < 1 at hlt
    change (parent S j.succ).val = 0
    omega
  have hkparent : parent S k.succ = 0 := by
    rcases Finset.mem_insert.mp (parent_mem_insert S k.succ) with hp0 | hpS
    · exact hp0
    · by_cases hp_ne : parent S k.succ = 0
      · exact hp_ne
      exfalso
      apply h1
      have hp_lt := parent_lt (S := S) (Fin.succ_pos k)
      have hp_eq : parent S k.succ = j.succ := by
        apply Fin.ext
        have hp_pos : 0 < (parent S k.succ).val :=
          Nat.pos_of_ne_zero (fun hv => hp_ne (Fin.ext hv))
        change (parent S k.succ).val < k.val + 1 at hp_lt
        change (parent S k.succ).val = j.val + 1
        dsimp only [j, k] at hp_lt ⊢
        omega
      rw [← hjchild, ← hp_eq]
      exact hpS
  have hroot : dot (A 0) u = 0 := by
    exact dot_insertZeroPerm_at (1 : Fin (r + 1 + 1)) τ
  have hjvalue : dot (A j.succ) u = 1 := by
    have hp : (1 : Fin (r + 1 + 1)) = (0 : Fin (r + 1)).succ := by
      apply Fin.ext
      change 1 % (r + 2) = 1
      rw [Nat.mod_eq_of_lt]
      omega
    exact dot_insertZeroPerm_of_ne 1 j.succ.succ τ (by
      intro h
      have he := Fin.succ_injective (r + 1) (h.trans hp)
      exact Fin.succ_ne_zero j he)
  have hkvalue : dot (A k.succ) u = 1 := by
    have hp : (1 : Fin (r + 1 + 1)) = (0 : Fin (r + 1)).succ := by
      apply Fin.ext
      change 1 % (r + 2) = 1
      rw [Nat.mod_eq_of_lt]
      omega
    exact dot_insertZeroPerm_of_ne 1 k.succ.succ τ (by
      intro h
      have he := Fin.succ_injective (r + 1) (h.trans hp)
      exact Fin.succ_ne_zero k he)
  apply germDiff_caterpillarUnit_mem_LSpan_of_two (toR (vtx (π 0))) A S
    (edgeVecs_simplex_injective (fun i => π i.succ)
      (π.injective.comp (Fin.succ_injective (r + 1))) S) u j k hjk
  · rw [hjparent, hroot, hjvalue]
    norm_num
  · rw [hkparent, hroot, hkvalue]
    norm_num

/-- A distinguished interior spine head which is not the last head has a
crossing edge entering it and a second crossing edge leaving it immediately. -/
theorem germDiff_insertZeroPerm_interior_head_mem_LSpan
    (τ : Equiv.Perm (Fin (r + 1))) (S : Finset (Fin (r + 1))) (j : Fin r)
    (hjS : j.succ ∈ S) (hjlast : j.succ ≠ Fin.last r) :
    germDiff (zeroCoordinateDirection (r + 1))
      (caterpillarUnit (toR (vtx ((insertZeroPerm j.succ.succ τ) 0)))
        (fun i => toR (vtx ((insertZeroPerm j.succ.succ τ) i.succ))) S) ∈
      LSpan (r + 1) (r - 1) := by
  let p : Fin (r + 1 + 1) := j.succ.succ
  let π := insertZeroPerm p τ
  let u := zeroCoordinateDirection (r + 1)
  let A : Fin (r + 1) → Fin (r + 1) → ℝ := fun i => toR (vtx (π i.succ))
  have hjbound : j.val + 1 < r := by
    have hjlt : j.succ < Fin.last r :=
      lt_of_le_of_ne (Fin.le_last j.succ) hjlast
    exact hjlt
  let k : Fin r := ⟨j.val + 1, hjbound⟩
  have hjk : j ≠ k := by
    intro h
    have := congrArg Fin.val h
    change j.val = j.val + 1 at this
    omega
  have hkval : k.val = j.val + 1 := by rfl
  have hkparent : parent S k.succ = j.succ := by
    apply Fin.ext
    have hlo : j.succ ≤ parent S k.succ := by
      apply le_parent_of_mem hjS
      change j.val + 1 < k.val + 1
      rw [hkval]
      omega
    have hhi := parent_lt (S := S) (show (0 : Fin (r + 1)) < k.succ from Fin.succ_pos k)
    change j.val + 1 ≤ (parent S k.succ).val at hlo
    change (parent S k.succ).val < k.val + 1 at hhi
    change (parent S k.succ).val = j.val + 1
    rw [hkval] at hhi
    apply Nat.le_antisymm
    · omega
    · exact hlo
  have hzero : dot (A j.succ) u = 0 := by
    exact dot_insertZeroPerm_at p τ
  have hparent_ne : (parent S j.succ).succ ≠ p := by
    intro he
    have hev := congrArg Fin.val he
    change (parent S j.succ).val + 1 = j.val + 2 at hev
    have hlt := parent_lt (S := S) (Fin.succ_pos j)
    change (parent S j.succ).val < j.val + 1 at hlt
    omega
  have hparent : dot (A (parent S j.succ)) u = 1 :=
    dot_insertZeroPerm_of_ne p (parent S j.succ).succ τ hparent_ne
  have hk_ne : k.succ.succ ≠ p := by
    intro he
    have hev := congrArg Fin.val he
    change k.val + 2 = j.val + 2 at hev
    rw [hkval] at hev
    omega
  have hkvalue : dot (A k.succ) u = 1 :=
    dot_insertZeroPerm_of_ne p k.succ.succ τ hk_ne
  apply germDiff_caterpillarUnit_mem_LSpan_of_two (toR (vtx (π 0))) A S
    (edgeVecs_simplex_injective (fun i => π i.succ)
      (π.injective.comp (Fin.succ_injective (r + 1))) S) u j k hjk
  · rw [hparent, hzero]
    norm_num
  · rw [hkparent, hzero, hkvalue]
    norm_num

end MaxNN.Caterpillar
