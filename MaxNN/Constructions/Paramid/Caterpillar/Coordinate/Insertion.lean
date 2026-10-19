import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Endpoints
import Mathlib.Algebra.BigOperators.Fin

/-! # Inserting a pendant vertex into an ordered caterpillar word -/

namespace MaxNN.Caterpillar

open BigOperators ParamidGeom

variable {s : ℕ}

/-- The new position immediately after a lower-word position. -/
def pendantPos (i : Fin (s + 1)) : Fin (s + 1 + 1) := i.succ

/-- Lift every old cut through the new pendant position.  The new position is
not a cut, hence it is a pendant vertex. -/
def insertPendantCuts (i : Fin (s + 1)) (S : Finset (Fin (s + 1))) :
    Finset (Fin (s + 1 + 1)) :=
  S.image (pendantPos i).succAbove

theorem pendantPos_ne_zero (i : Fin (s + 1)) : pendantPos i ≠ 0 :=
  Fin.succ_ne_zero i

theorem insertPendantCuts_not_mem (i : Fin (s + 1)) (S : Finset (Fin (s + 1))) :
    pendantPos i ∉ insertPendantCuts i S := by
  intro h
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp h
  exact Fin.succAbove_ne _ _ hq

theorem mem_insertPendantCuts (i : Fin (s + 1)) (S : Finset (Fin (s + 1)))
    (q : Fin (s + 1)) (hq : q ∈ S) :
    (pendantPos i).succAbove q ∈ insertPendantCuts i S :=
  Finset.mem_image.mpr ⟨q, hq, rfl⟩

theorem pendant_succAbove_zero (i : Fin (s + 1)) :
    (pendantPos i).succAbove (0 : Fin (s + 1)) = 0 := by
  exact Fin.succAbove_ne_zero_zero (pendantPos_ne_zero i)

theorem parent_insertPendantCuts_lift (i : Fin (s + 1))
    (S : Finset (Fin (s + 1))) (q : Fin (s + 1)) (hq : 0 < q) :
    parent (insertPendantCuts i S) ((pendantPos i).succAbove q) =
      (pendantPos i).succAbove (parent S q) := by
  let e := (Fin.succAboveEmb (pendantPos i))
  apply le_antisymm
  · rcases Finset.mem_insert.mp
        (parent_mem_insert (insertPendantCuts i S) ((pendantPos i).succAbove q)) with hz | hu
    · rw [hz]
      exact Fin.zero_le _
    · obtain ⟨a, haS, ha⟩ := Finset.mem_image.mp hu
      have halt : e a < e q := by
        change (pendantPos i).succAbove a < (pendantPos i).succAbove q
        rw [ha]
        exact parent_lt (Fin.succAbove_pos (pendantPos i) q hq)
      have haq : a < q := e.lt_iff_lt.mp halt
      change parent (insertPendantCuts i S) ((pendantPos i).succAbove q) ≤
        (pendantPos i).succAbove (parent S q)
      rw [← ha]
      exact e.monotone (le_parent_of_mem haS haq)
  · rcases Finset.mem_insert.mp (parent_mem_insert S q) with hz | hpS
    · rw [hz, pendant_succAbove_zero]
      exact Fin.zero_le _
    · exact le_parent_of_mem (mem_insertPendantCuts i S _ hpS)
        ((Fin.succAboveEmb (pendantPos i)).lt_iff_lt.mpr (parent_lt hq))

theorem lastHead_insertPendantCuts (i : Fin (s + 1))
    (S : Finset (Fin (s + 1))) :
    lastHead (insertPendantCuts i S) = (pendantPos i).succAbove (lastHead S) := by
  let e := (Fin.succAboveEmb (pendantPos i))
  apply le_antisymm
  · have hm := Finset.max'_mem (insert 0 (insertPendantCuts i S))
        (Finset.insert_nonempty _ _)
    change lastHead (insertPendantCuts i S) ∈ insert 0 (insertPendantCuts i S) at hm
    rcases Finset.mem_insert.mp hm with hz | hu
    · rw [hz]
      exact Fin.zero_le _
    · obtain ⟨a, haS, ha⟩ := Finset.mem_image.mp hu
      change lastHead (insertPendantCuts i S) ≤
        (pendantPos i).succAbove (lastHead S)
      rw [← ha]
      exact e.monotone (Finset.le_max' _ a (Finset.mem_insert_of_mem haS))
  · have hm := Finset.max'_mem (insert 0 S) (Finset.insert_nonempty _ _)
    change lastHead S ∈ insert 0 S at hm
    rcases Finset.mem_insert.mp hm with hz | hS
    · rw [hz, pendant_succAbove_zero]
      exact Fin.zero_le _
    · exact Finset.le_max' _ _
        (Finset.mem_insert_of_mem (mem_insertPendantCuts i S _ hS))

/-- Insert the exceptional vertex in the corresponding word slot. -/
def insertPendantWord {X : Type*} (i : Fin (s + 1)) (b : X)
    (A : Fin (s + 1) → X) : Fin (s + 1 + 1) → X :=
  Fin.insertNth (pendantPos i) b (fun q => A q)

@[simp] theorem insertPendantWord_at (i : Fin (s + 1)) (b : X)
    (A : Fin (s + 1) → X) : insertPendantWord i b A (pendantPos i) = b := by
  exact Fin.insertNth_apply_same _ _ _

@[simp] theorem insertPendantWord_lift (i : Fin (s + 1)) (b : X)
    (A : Fin (s + 1) → X) (q : Fin (s + 1)) :
    insertPendantWord i b A ((pendantPos i).succAbove q) = A q := by
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem insertPendantWord_of_ne (i : Fin (s + 1)) (b : X)
    (A : Fin (s + 1) → X) (q : Fin (s + 1 + 1)) (hq : q ≠ pendantPos i) :
    ∃ a, q = (pendantPos i).succAbove a ∧ insertPendantWord i b A q = A a := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hq
  refine ⟨a, ha.symm, ?_⟩
  rw [← ha]
  exact insertPendantWord_lift i b A a

theorem card_insertPendantCuts (i : Fin (s + 1)) (S : Finset (Fin (s + 1))) :
    (insertPendantCuts i S).card = S.card := by
  exact Finset.card_image_of_injective _ Fin.succAbove_right_injective

theorem insertPendantCuts_mem_admissible (i : Fin (s + 1))
    (S : Finset (Fin (s + 1))) (hS : S ∈ admissibleCuts s) :
    insertPendantCuts i S ∈ admissibleCuts (s + 1) := by
  have hS' : S ∈ (cutPositions s).powerset.erase ∅ := by
    simpa only [admissibleCuts] using hS
  have hpowerset : S ⊆ cutPositions s :=
    Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS')
  have hnonempty : S.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS').1
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_powerset.mpr ?_⟩
  · exact (hnonempty.image _).ne_empty
  · intro q hq
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hq
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp (hpowerset haS)).1
    apply Finset.mem_erase.mpr
    exact ⟨Fin.succAbove_ne_zero (pendantPos_ne_zero i) ha0, Finset.mem_univ _⟩

/-- At the negative coordinate normal, the exposed base face deletes an
inserted pendant vertex exactly. -/
theorem baseGerm_insertPendant_neg
    (i : Fin (s + 1)) (b : Fin m → ℝ) (A : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (s + 1))) (u : Fin m → ℝ)
    (hb : dot b u = 0) (hA : ∀ q, dot (A q) u = 1) :
    baseGerm (insertPendantWord i b A) (insertPendantCuts i S) (-u) =
      fun y => baseMax (values A y) S := by
  let p : Fin (s + 1 + 1) := pendantPos i
  let U : Finset (Fin (s + 1 + 1)) := insertPendantCuts i S
  let W : Fin (s + 1 + 1) → Fin m → ℝ := insertPendantWord i b A
  have hpU : p ∉ U := insertPendantCuts_not_mem i S
  have hparent_ne : parent U p ≠ p := by
    exact parent_ne_pendant U i hpU p
  have hparent : dot (W (parent U p)) u = 1 := by
    obtain ⟨a, _, ha⟩ := insertPendantWord_of_ne i b A _ hparent_ne
    change dot (insertPendantWord i b A (parent U p)) u = 1
    rw [ha, hA]
  have hWp : W p = b := by
    change insertPendantWord i b A (pendantPos i) = b
    exact insertPendantWord_at i b A
  have hedge_p : pairGerm (W (parent U p)) (W p) (-u) = dot b := by
    funext y
    unfold pairGerm
    rw [UnitGermAux.dot_neg_right, UnitGermAux.dot_neg_right, hparent]
    change (if -(1 : ℝ) < -dot (W p) u then dot (W p) y
      else if -dot (W p) u < -1 then dot (W (parent U p)) y
      else max (dot (W (parent U p)) y) (dot (W p) y)) = dot b y
    rw [hWp, hb]
    norm_num
  have hedge_lift : ∀ q : Fin s,
      pairGerm (W (parent U ((i.succAbove q).succ))) (W ((i.succAbove q).succ)) (-u) =
        fun y => max (dot (A (parent S q.succ)) y) (dot (A q.succ) y) := by
    intro q
    have hchild : (i.succAbove q).succ = p.succAbove q.succ := by
      exact (Fin.succ_succAbove_succ i q).symm
    have hpar : parent U ((i.succAbove q).succ) = p.succAbove (parent S q.succ) := by
      rw [hchild]
      exact parent_insertPendantCuts_lift i S q.succ (Fin.succ_pos q)
    have hwpar : W (p.succAbove (parent S q.succ)) = A (parent S q.succ) := by
      change insertPendantWord i b A ((pendantPos i).succAbove (parent S q.succ)) = _
      exact insertPendantWord_lift i b A _
    have hwchild : W (p.succAbove q.succ) = A q.succ := by
      change insertPendantWord i b A ((pendantPos i).succAbove q.succ) = _
      exact insertPendantWord_lift i b A _
    funext y
    unfold pairGerm
    rw [hpar, hchild, hwpar, hwchild,
      UnitGermAux.dot_neg_right, UnitGermAux.dot_neg_right, hA, hA]
    norm_num
  have hedge_sum : (∑ k : Fin (s + 1),
      pairGerm (W (parent U k.succ)) (W k.succ) (-u)) =
      dot b + ∑ q : Fin s, fun y =>
        max (dot (A (parent S q.succ)) y) (dot (A q.succ) y) := by
    rw [Fin.sum_univ_succAbove (fun k : Fin (s + 1) =>
      pairGerm (W (parent U k.succ)) (W k.succ) (-u)) i]
    change pairGerm (W (parent U p)) (W p) (-u) + _ = _
    rw [hedge_p]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    exact hedge_lift q
  have hvertex_sum (y : Fin m → ℝ) : (∑ q : Fin (s + 1 + 1), dot (W q) y) =
      dot b y + ∑ q : Fin (s + 1), dot (A q) y := by
    rw [Fin.sum_univ_succAbove (fun q : Fin (s + 1 + 1) => dot (W q) y) p]
    simp only [W, p, insertPendantWord_at, insertPendantWord_lift]
  have hroot : W 0 = A 0 := by
    rw [← pendant_succAbove_zero i]
    exact insertPendantWord_lift i b A 0
  have hlast : W (lastHead U) = A (lastHead S) := by
    change insertPendantWord i b A (lastHead (insertPendantCuts i S)) = A (lastHead S)
    rw [lastHead_insertPendantCuts, insertPendantWord_lift]
  funext y
  unfold baseGerm baseMax pointedMax
  change (∑ k : Fin (s + 1), pairGerm (W (parent U k.succ)) (W k.succ) (-u) y) -
      (∑ q : Fin (s + 1 + 1), dot (W q) y) + dot (W 0) y +
        dot (W (lastHead U)) y = _
  rw [← Finset.sum_apply, hedge_sum, Pi.add_apply, Finset.sum_apply,
    hvertex_sum, hroot, hlast]
  simp only [treeMax, values]
  ring

/-- Every pendant insertion contributes one negative copy of the lower word
to the coordinate facet datum, modulo segment support functions. -/
theorem germDiff_insertPendant_add_lower_mem_LSpan_one
    (i : Fin (s + 1)) (apex b : Fin m → ℝ)
    (A : Fin (s + 1) → Fin m → ℝ) (S : Finset (Fin (s + 1)))
    (u : Fin m → ℝ) (ha : dot apex u = 1) (hb : dot b u = 0)
    (hA : ∀ q, dot (A q) u = 1) :
    germDiff u (caterpillarUnit apex (insertPendantWord i b A)
        (insertPendantCuts i S)) + caterpillarUnit apex A S ∈ LSpan m 1 := by
  have hother : ∀ q : Fin (s + 1 + 1), q ≠ (pendantPos i) →
      dot (insertPendantWord i b A q) u = 1 := by
    intro q hq
    obtain ⟨a, _, haWord⟩ := insertPendantWord_of_ne i b A q hq
    rw [haWord, hA]
  have h := germDiff_add_coordinatePendantFace_mem_LSpan_one apex
    (insertPendantWord i b A) (insertPendantCuts i S) i
    (insertPendantCuts_not_mem i S) u ha (by
      simpa only [pendantPos, insertPendantWord, Fin.insertNth_apply_same] using hb) hother
  have hface : (fun y => max (dot apex y)
      (baseGerm (insertPendantWord i b A) (insertPendantCuts i S) (-u) y)) =
      caterpillarUnit apex A S := by
    rw [baseGerm_insertPendant_neg i b A S u hb hA]
    rfl
  rwa [hface] at h

end MaxNN.Caterpillar
