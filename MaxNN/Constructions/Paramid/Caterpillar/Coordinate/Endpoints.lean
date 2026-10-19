import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Unit
import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Join

/-! # Deleting a coordinate vertex at a spine endpoint

Appending the exceptional coordinate vertex as either endpoint of the base
word gives an upper-arity germ which is exactly the lower-arity caterpillar
unit.  These are pointwise function equalities, before taking classes modulo
lower-dimensional support functions.
-/

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m s : ℕ}

theorem germ_caterpillarUnit_coordinate_lastEndpoint
    (apex : Fin m → ℝ) (A : Fin (s + 1) → Fin m → ℝ) (b : Fin m → ℝ)
    (S : Finset (Fin (s + 1))) (u : Fin m → ℝ)
    (ha : dot apex u = 1) (hA : ∀ i, dot (A i) u = 1) (hb : dot b u = 0) :
    germ (caterpillarUnit (r := s + 1) apex
      (Fin.append (m := s + 1) (n := 1) A (fun _ => b))
      (joinCuts S (∅ : Finset (Fin 1)))) u =
      caterpillarUnit apex A S := by
  let B : Fin 1 → Fin m → ℝ := fun _ => b
  have hB : ∀ i, dot (B i) u = 0 := fun _ => hb
  have hcross' := isGerm_max_of_lt (isGerm_dot (B 0) u)
    (isGerm_dot (A (lastHead S)) u) (by rw [hA (lastHead S), hB 0]; norm_num)
  have hcross : IsGerm (fun y => max (dot (A (lastHead S)) y) (dot (B 0) y)) u
      (dot (A (lastHead S))) := by
    simpa only [max_comm] using hcross'
  have hinner := (((isGerm_pointedMax_of_constant A S u 1 hA).add
    (isGerm_baseMax_of_constant B (∅ : Finset (Fin 1)) u 0 hB)).add hcross).sub
      (isGerm_dot (B 0) u)
  have hvA : pointedMax (values A u) S = 0 := pointedMax_of_constant _ _ 1 hA
  have hvB : baseMax (values B u) (∅ : Finset (Fin 1)) = 0 :=
    baseMax_of_constant _ _ 0 hB
  have hout := isGerm_max_of_eq (isGerm_dot apex u) hinner (by
    change dot apex u = pointedMax (values A u) S +
      baseMax (values B u) (∅ : Finset (Fin 1)) +
      max (dot (A (lastHead S)) u) (dot (B 0) u) - dot (B 0) u
    rw [ha, hvA, hvB, hA (lastHead S), hB 0]
    norm_num)
  rw [caterpillarUnit_join]
  apply germ_eq_of_isGerm
  convert hout using 1
  funext y
  unfold caterpillarUnit
  change max (dot apex y) (baseMax (values A y) S) =
    max (dot apex y) (pointedMax (values A y) S +
      baseMax (values B y) (∅ : Finset (Fin 1)) +
      dot (A (lastHead S)) y - dot (B 0) y)
  have hsingle : baseMax (values B y) (∅ : Finset (Fin 1)) = dot (B 0) y := by
    change baseMax (fun _ : Fin 1 => dot b y) (∅ : Finset (Fin 1)) = dot b y
    simp [baseMax, pointedMax, treeMax, lastHead, parent]
  rw [hsingle]
  unfold baseMax
  simp only [values]
  ring

theorem germDiff_lastEndpoint_sub_lower_mem_LSpan_one
    (apex : Fin m → ℝ) (A : Fin (s + 1) → Fin m → ℝ) (b : Fin m → ℝ)
    (S : Finset (Fin (s + 1))) (u : Fin m → ℝ)
    (ha : dot apex u = 1) (hA : ∀ i, dot (A i) u = 1) (hb : dot b u = 0) :
    germDiff u (caterpillarUnit (r := s + 1) apex
        (Fin.append (m := s + 1) (n := 1) A (fun _ => b))
        (joinCuts S (∅ : Finset (Fin 1)))) - caterpillarUnit apex A S ∈ LSpan m 1 := by
  let B : Fin 1 → Fin m → ℝ := fun _ => b
  let W := Fin.append (m := s + 1) (n := 1) A B
  let U := joinCuts S (∅ : Finset (Fin 1))
  have hAneg : ∀ i, dot (A i) (-u) = -1 := by
    intro i
    rw [UnitGermAux.dot_neg_right, hA i]
  have hBneg : ∀ i, dot (B i) (-u) = 0 := by
    intro i
    rw [UnitGermAux.dot_neg_right, hb, neg_zero]
  have hvAneg : ∀ i, values A (-u) i = -1 := hAneg
  have hvBneg : ∀ i, values B (-u) i = 0 := hBneg
  have hbase : baseMax (values W (-u)) U = 0 := by
    rw [show values W (-u) = Fin.append (values A (-u)) (values B (-u)) by
      exact values_append A B (-u), baseMax_join]
    rw [pointedMax_of_constant _ _ (-1) hvAneg,
      baseMax_of_constant _ _ 0 hvBneg, hvAneg, hvBneg]
    norm_num
  have hn : germ (caterpillarUnit apex W U) (-u) ∈ LSpan m 1 :=
    germ_caterpillarUnit_mem_LSpan_one_of_ne apex W U (-u) (by
      rw [UnitGermAux.dot_neg_right, ha, hbase]
      norm_num)
  have hp := germ_caterpillarUnit_coordinate_lastEndpoint apex A b S u ha hA hb
  have hp' : germ (caterpillarUnit apex W U) u = caterpillarUnit apex A S := by
    simpa only [W, U, B] using hp
  have he : germDiff u (caterpillarUnit apex W U) - caterpillarUnit apex A S =
      -germ (caterpillarUnit apex W U) (-u) := by
    funext y
    unfold germDiff
    simp only [Pi.sub_apply, Pi.neg_apply]
    rw [congrFun hp' y]
    ring
  change germDiff u (caterpillarUnit apex W U) - caterpillarUnit apex A S ∈ LSpan m 1
  rw [he]
  exact Submodule.neg_mem _ hn

theorem germ_caterpillarUnit_coordinate_firstEndpoint
    (apex b : Fin m → ℝ) (A : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (s + 1))) (u : Fin m → ℝ)
    (ha : dot apex u = 1) (hb : dot b u = 0) (hA : ∀ i, dot (A i) u = 1) :
    germ (caterpillarUnit (r := 1 + s) apex
      (Fin.append (m := 1) (n := s + 1) (fun _ => b) A)
      (joinCuts (∅ : Finset (Fin 1)) S)) u =
      caterpillarUnit apex A S := by
  let B : Fin 1 → Fin m → ℝ := fun _ => b
  have hB : ∀ i, dot (B i) u = 0 := fun _ => hb
  have hlast : lastHead (∅ : Finset (Fin 1)) = 0 := by
    simp [lastHead]
  have hBlast : dot (B (lastHead (∅ : Finset (Fin 1)))) u = 0 := by
    rw [hlast]
    exact hB 0
  have hcross := isGerm_max_of_lt
    (isGerm_dot (B (lastHead (∅ : Finset (Fin 1)))) u)
    (isGerm_dot (A 0) u) (by rw [hBlast, hA 0]; norm_num)
  have hinner := (((isGerm_pointedMax_of_constant B (∅ : Finset (Fin 1)) u 0 hB).add
    (isGerm_baseMax_of_constant A S u 1 hA)).add hcross).sub (isGerm_dot (A 0) u)
  have hvB : pointedMax (values B u) (∅ : Finset (Fin 1)) = 0 :=
    pointedMax_of_constant _ _ 0 hB
  have hvA : baseMax (values A u) S = 1 := baseMax_of_constant _ _ 1 hA
  have hout := isGerm_max_of_eq (isGerm_dot apex u) hinner (by
    change dot apex u = pointedMax (values B u) (∅ : Finset (Fin 1)) +
      baseMax (values A u) S +
      max (dot (B (lastHead (∅ : Finset (Fin 1)))) u) (dot (A 0) u) - dot (A 0) u
    rw [ha, hvB, hvA, hBlast, hA 0]
    norm_num)
  rw [caterpillarUnit_join]
  apply germ_eq_of_isGerm
  convert hout using 1
  funext y
  unfold caterpillarUnit
  change max (dot apex y) (baseMax (values A y) S) =
    max (dot apex y) (pointedMax (values B y) (∅ : Finset (Fin 1)) +
      baseMax (values A y) S +
      dot (A 0) y - dot (A 0) y)
  have hzero : pointedMax (values B y) (∅ : Finset (Fin 1)) = 0 := by
    change pointedMax (fun _ : Fin 1 => dot b y) (∅ : Finset (Fin 1)) = 0
    simp [pointedMax, treeMax, parent]
  rw [hzero]
  ring_nf

theorem germDiff_firstEndpoint_sub_lower_mem_LSpan_one
    (apex b : Fin m → ℝ) (A : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (s + 1))) (u : Fin m → ℝ)
    (ha : dot apex u = 1) (hb : dot b u = 0) (hA : ∀ i, dot (A i) u = 1) :
    germDiff u (caterpillarUnit (r := 1 + s) apex
        (Fin.append (m := 1) (n := s + 1) (fun _ => b) A)
        (joinCuts (∅ : Finset (Fin 1)) S)) - caterpillarUnit apex A S ∈ LSpan m 1 := by
  let B : Fin 1 → Fin m → ℝ := fun _ => b
  let W := Fin.append (m := 1) (n := s + 1) B A
  let U := joinCuts (∅ : Finset (Fin 1)) S
  have hAneg : ∀ i, dot (A i) (-u) = -1 := by
    intro i
    rw [UnitGermAux.dot_neg_right, hA i]
  have hBneg : ∀ i, dot (B i) (-u) = 0 := by
    intro i
    rw [UnitGermAux.dot_neg_right, hb, neg_zero]
  have hvAneg : ∀ i, values A (-u) i = -1 := hAneg
  have hvBneg : ∀ i, values B (-u) i = 0 := hBneg
  have hbase : baseMax (values W (-u)) U = 0 := by
    rw [show values W (-u) = Fin.append (values B (-u)) (values A (-u)) by
      exact values_append B A (-u), baseMax_join]
    rw [pointedMax_of_constant _ _ 0 hvBneg,
      baseMax_of_constant _ _ (-1) hvAneg, hvBneg, hvAneg]
    norm_num
  have hn : germ (caterpillarUnit apex W U) (-u) ∈ LSpan m 1 :=
    germ_caterpillarUnit_mem_LSpan_one_of_ne apex W U (-u) (by
      rw [UnitGermAux.dot_neg_right, ha, hbase]
      norm_num)
  have hp := germ_caterpillarUnit_coordinate_firstEndpoint apex b A S u ha hb hA
  have hp' : germ (caterpillarUnit apex W U) u = caterpillarUnit apex A S := by
    simpa only [W, U, B] using hp
  have he : germDiff u (caterpillarUnit apex W U) - caterpillarUnit apex A S =
      -germ (caterpillarUnit apex W U) (-u) := by
    funext y
    unfold germDiff
    simp only [Pi.sub_apply, Pi.neg_apply]
    rw [congrFun hp' y]
    ring
  change germDiff u (caterpillarUnit apex W U) - caterpillarUnit apex A S ∈ LSpan m 1
  rw [he]
  exact Submodule.neg_mem _ hn

end MaxNN.Caterpillar
