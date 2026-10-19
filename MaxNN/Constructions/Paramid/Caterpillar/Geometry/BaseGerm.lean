import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Germ

/-! # Direct germs of caterpillar bases

Each pair maximum has an explicit three-case germ. Finite sums give the germ
of the whole base, which lies in `LSpan m 1` in every direction. Consequently,
when the outer apex/base maximum is strict, the germ of the unit also lies in
`LSpan m 1`. These are local statements, not the global caterpillar identity.
-/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m r : ℕ}

/-- The exposed endpoint, or the whole segment when the endpoints tie. -/
noncomputable def pairGerm (a b u : Fin m → ℝ) (y : Fin m → ℝ) : ℝ :=
  if dot a u < dot b u then dot b y
  else if dot b u < dot a u then dot a y
  else max (dot a y) (dot b y)

theorem isGerm_pairMax (a b u : Fin m → ℝ) :
    IsGerm (fun y => max (dot a y) (dot b y)) u (pairGerm a b u) := by
  unfold pairGerm
  split_ifs with hab hba
  · exact isGerm_max_of_lt (isGerm_dot a u) (isGerm_dot b u) hab
  · simpa only [max_comm] using
      isGerm_max_of_lt (isGerm_dot b u) (isGerm_dot a u) hba
  · exact isGerm_max_of_eq (isGerm_dot a u) (isGerm_dot b u)
      (le_antisymm (not_lt.mp hba) (not_lt.mp hab))

theorem pairGerm_mem_LSpan_one (a b u : Fin m → ℝ) :
    pairGerm a b u ∈ LSpan m 1 := by
  unfold pairGerm
  split_ifs
  · exact UnitGermAux.dot_mem_LSpan _ _
  · exact UnitGermAux.dot_mem_LSpan _ _
  · exact max_dot_mem_LSpan_one a b

/-- An explicit finite formula for the germ, with the original linear terms. -/
noncomputable def baseGerm (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (u y : Fin m → ℝ) : ℝ :=
  (∑ j : Fin r, pairGerm (A (parent S j.succ)) (A j.succ) u y) -
    (∑ i, dot (A i) y) + dot (A 0) y + dot (A (lastHead S)) y

theorem isGerm_baseMax (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (u : Fin m → ℝ) :
    IsGerm (fun y => baseMax (values A y) S) u (baseGerm A S u) := by
  have ht : IsGerm (fun y => treeMax (values A y) S) u
      (fun y => ∑ j : Fin r, pairGerm (A (parent S j.succ)) (A j.succ) u y) := by
    apply IsGerm.sum
    intro j _
    exact isGerm_pairMax (A (parent S j.succ)) (A j.succ) u
  have hl : IsGerm (fun y => ∑ i : Fin (r + 1), dot (A i) y) u
      (fun y => ∑ i : Fin (r + 1), dot (A i) y) :=
    IsGerm.sum Finset.univ fun i _ => isGerm_dot (A i) u
  exact ((ht.sub hl).add (isGerm_dot (A 0) u)).add (isGerm_dot (A (lastHead S)) u)

theorem baseGerm_mem_LSpan_one (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (u : Fin m → ℝ) : baseGerm A S u ∈ LSpan m 1 := by
  have hp : (∑ j : Fin r, pairGerm (A (parent S j.succ)) (A j.succ) u) ∈ LSpan m 1 :=
    Submodule.sum_mem _ fun _ _ => pairGerm_mem_LSpan_one _ _ _
  have hl : (∑ i, dot (A i)) ∈ LSpan m 1 :=
    Submodule.sum_mem _ fun _ _ => UnitGermAux.dot_mem_LSpan _ _
  have h := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ hp hl)
    (UnitGermAux.dot_mem_LSpan (A 0) 1))
      (UnitGermAux.dot_mem_LSpan (A (lastHead S)) 1)
  have he : baseGerm A S u = (∑ j : Fin r, pairGerm (A (parent S j.succ)) (A j.succ) u) -
      (∑ i, dot (A i)) + dot (A 0) + dot (A (lastHead S)) := by
    funext y
    simp only [baseGerm, Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  rwa [he]

theorem germ_baseMax_mem_LSpan_one (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (u : Fin m → ℝ) :
    germ (fun y => baseMax (values A y) S) u ∈ LSpan m 1 := by
  rw [germ_eq_of_isGerm (isGerm_baseMax A S u)]
  exact baseGerm_mem_LSpan_one A S u

/-- One actual two-level maximum in the caterpillar candidate. -/
noncomputable def caterpillarUnit (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (y : Fin m → ℝ) : ℝ :=
  max (dot apex y) (baseMax (values A y) S)

theorem germ_caterpillarUnit_mem_LSpan_one_of_ne (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (S : Finset (Fin (r + 1))) (u : Fin m → ℝ)
    (hne : dot apex u ≠ baseMax (values A u) S) :
    germ (caterpillarUnit apex A S) u ∈ LSpan m 1 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := isGerm_max_of_lt (isGerm_dot apex u) (isGerm_baseMax A S u) hlt
    change germ (fun y => max (dot apex y) (baseMax (values A y) S)) u ∈ LSpan m 1
    rw [germ_eq_of_isGerm h]
    exact baseGerm_mem_LSpan_one A S u
  · have h := isGerm_max_of_lt (isGerm_baseMax A S u) (isGerm_dot apex u) hgt
    have he : caterpillarUnit apex A S =
        fun y => max (baseMax (values A y) S) (dot apex y) := by
      funext y
      exact max_comm _ _
    rw [he, germ_eq_of_isGerm h]
    exact UnitGermAux.dot_mem_LSpan _ _

end MaxNN.Caterpillar
