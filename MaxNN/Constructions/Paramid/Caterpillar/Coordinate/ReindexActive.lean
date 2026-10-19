import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Active
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.ReindexCuts

/-! # Reindexing the active coordinate fibres -/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {s : ℕ}

noncomputable local instance coordinateActiveDecidable' (p : Fin (s + 3))
    (U : Finset (Fin (s + 2))) : Decidable (coordinateActive p U) :=
  Classical.propDecidable _

abbrev LowerAdmissibleCuts (s : ℕ) :=
  {S : Finset (Fin (s + 1)) // S ∈ admissibleCuts s}

abbrev LowerCutSubsets (s : ℕ) :=
  {S : Finset (Fin (s + 1)) // S ⊆ cutPositions s}

abbrev UpperAdmissibleCuts (s : ℕ) :=
  {U : Finset (Fin (s + 2)) // U ∈ admissibleCuts (s + 1)}

abbrev CoordinateActiveIndex (s : ℕ) :=
  {q : Fin (s + 3) × UpperAdmissibleCuts s // coordinateActive q.1 q.2.1}

abbrev CoordinateFibreIndex (s : ℕ) :=
  LowerCutSubsets s ⊕ ((Fin (s + 1) × LowerAdmissibleCuts s) ⊕ LowerCutSubsets s)

noncomputable def coordinateFibreToActive :
    CoordinateFibreIndex s → CoordinateActiveIndex s
  | Sum.inl S =>
      ⟨⟨1, ⟨firstInsertCuts S.1, firstInsertCuts_mem_admissible S.1 S.2⟩⟩,
        Or.inl ⟨rfl, one_mem_firstInsertCuts S.1⟩⟩
  | Sum.inr (Sum.inl q) =>
      ⟨⟨(pendantPos q.1).succ,
        ⟨insertPendantCuts q.1 q.2.1,
          insertPendantCuts_mem_admissible q.1 q.2.1 q.2.2⟩⟩,
        Or.inr ⟨q.1, rfl, Or.inl (insertPendantCuts_not_mem q.1 q.2.1)⟩⟩
  | Sum.inr (Sum.inr S) =>
      ⟨⟨Fin.last (s + 2),
        ⟨joinCuts (s := 0) S.1 (∅ : Finset (Fin 1)),
          joinCuts_empty_mem_admissible S.1 S.2⟩⟩,
        Or.inr ⟨Fin.last s, by apply Fin.ext; rfl,
          Or.inr (by apply Fin.ext; rfl)⟩⟩

private theorem coordinateFibreToActive_injective :
    Function.Injective (@coordinateFibreToActive s) := by
  intro x y hxy
  rcases x with S | q
  · rcases y with T | q'
    · congr 1
      apply (firstCutsEquiv (s := s)).injective
      apply Subtype.ext
      exact congrArg (fun z : CoordinateActiveIndex s => z.1.2.1) hxy
    · rcases q' with q' | T
      · have hp := congrArg (fun z : CoordinateActiveIndex s => z.1.1.val) hxy
        change (1 : Fin (s + 3)).val = ((pendantPos q'.1).succ).val at hp
        simp only [pendantPos] at hp
        have hone : (1 : Fin (s + 3)).val = 1 := by
          change 1 % (s + 3) = 1
          rw [Nat.mod_eq_of_lt]
          omega
        rw [hone] at hp
        change 1 = q'.1.val + 2 at hp
        omega
      · have hp := congrArg (fun z : CoordinateActiveIndex s => z.1.1.val) hxy
        change (1 : Fin (s + 3)).val = (Fin.last (s + 2)).val at hp
        have hone : (1 : Fin (s + 3)).val = 1 := by
          change 1 % (s + 3) = 1
          rw [Nat.mod_eq_of_lt]
          omega
        rw [hone] at hp
        change 1 = s + 2 at hp
        omega
  · rcases q with q | S
    · rcases q with ⟨i, S⟩
      rcases y with T | q'
      · have hp := congrArg (fun z : CoordinateActiveIndex s => z.1.1.val) hxy
        change ((pendantPos i).succ).val = (1 : Fin (s + 3)).val at hp
        simp only [pendantPos] at hp
        have hone : (1 : Fin (s + 3)).val = 1 := by
          change 1 % (s + 3) = 1
          rw [Nat.mod_eq_of_lt]
          omega
        rw [hone] at hp
        change i.val + 2 = 1 at hp
        omega
      · rcases q' with q' | T
        · rcases q' with ⟨i', T⟩
          have hp := congrArg (fun z : CoordinateActiveIndex s => z.1.1) hxy
          have hi : i = i' := by
            apply Fin.ext
            have hv := congrArg Fin.val hp
            simp only [pendantPos] at hv
            change i.val + 2 = i'.val + 2 at hv
            exact Nat.add_right_cancel hv
          subst i'
          apply congrArg Sum.inr
          apply congrArg Sum.inl
          apply Prod.ext
          · rfl
          · apply (pendantCutsEquiv i).injective
            apply Subtype.ext
            exact congrArg (fun z : CoordinateActiveIndex s => z.1.2.1) hxy
        · have hcuts := congrArg (fun z : CoordinateActiveIndex s => z.1.2.1) hxy
          have hp := congrArg (fun z : CoordinateActiveIndex s => z.1.1) hxy
          have hi : i = Fin.last s := by
            apply Fin.ext
            have hv := congrArg Fin.val hp
            simp only [pendantPos] at hv
            change i.val + 2 = s + 2 at hv
            change i.val = s
            exact Nat.add_right_cancel hv
          subst i
          have hnot := insertPendantCuts_not_mem (Fin.last s) S.1
          apply False.elim
          apply hnot
          change insertPendantCuts (Fin.last s) S.1 =
            joinCuts (s := 0) T.1 (∅ : Finset (Fin 1)) at hcuts
          rw [hcuts]
          exact last_mem_joinCuts_empty T.1
    · rcases y with T | q'
      · have hp := congrArg (fun z : CoordinateActiveIndex s => z.1.1.val) hxy
        change (Fin.last (s + 2)).val = (1 : Fin (s + 3)).val at hp
        have hone : (1 : Fin (s + 3)).val = 1 := by
          change 1 % (s + 3) = 1
          rw [Nat.mod_eq_of_lt]
          omega
        rw [hone] at hp
        change s + 2 = 1 at hp
        omega
      · rcases q' with q' | T
        · rcases q' with ⟨i, T'⟩
          have hcuts := congrArg (fun z : CoordinateActiveIndex s => z.1.2.1) hxy
          have hp := congrArg (fun z : CoordinateActiveIndex s => z.1.1) hxy
          have hi : i = Fin.last s := by
            apply Fin.ext
            have hv := congrArg Fin.val hp
            simp only [pendantPos] at hv
            change s + 2 = i.val + 2 at hv
            change i.val = s
            exact (Nat.add_right_cancel hv).symm
          subst i
          have hnot := insertPendantCuts_not_mem (Fin.last s) T'.1
          apply False.elim
          apply hnot
          change joinCuts (s := 0) S.1 (∅ : Finset (Fin 1)) =
            insertPendantCuts (Fin.last s) T'.1 at hcuts
          rw [← hcuts]
          exact last_mem_joinCuts_empty S.1
        · congr 2
          apply (lastCutsEquiv (s := s)).injective
          apply Subtype.ext
          exact congrArg (fun z : CoordinateActiveIndex s => z.1.2.1) hxy

private theorem coordinateFibreToActive_surjective :
    Function.Surjective (@coordinateFibreToActive s) := by
  intro q
  rcases q with ⟨⟨p, U⟩, ha⟩
  rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨k, rfl⟩
  · exact False.elim (by
      rcases ha with ⟨hp, _⟩ | ⟨j, hp, _⟩
      · exact Fin.zero_ne_one hp
      · have hv := congrArg Fin.val hp
        simp only [pendantPos] at hv
        change 0 = j.val + 2 at hv
        omega)
  · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · have h1 : (1 : Fin (s + 2)) ∈ U.1 := by
        rcases ha with hfirst | ⟨j, hp, _⟩
        · exact hfirst.2
        · have hv := congrArg Fin.val hp
          simp only [pendantPos] at hv
          change 1 = j.val + 2 at hv
          omega
      let T := (firstCutsEquiv (s := s)).symm ⟨U.1, U.2, h1⟩
      refine ⟨Sum.inl T, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change firstInsertCuts T.1 = U.1
        exact congrArg Subtype.val ((firstCutsEquiv (s := s)).apply_symm_apply
          ⟨U.1, U.2, h1⟩)
    · by_cases hiU : i.succ ∈ U.1
      · have hilast : i.succ = Fin.last (s + 1) := by
          rcases ha with ⟨hp, _⟩ | ⟨j, hp, hj⟩
          · have hv := congrArg Fin.val hp
            change i.val + 2 = 1 % (s + 3) at hv
            have hone : 1 % (s + 3) = 1 := Nat.mod_eq_of_lt (by omega)
            rw [hone] at hv
            omega
          · have hji : j = i := by
              apply Fin.ext
              have hv := congrArg Fin.val hp
              simp only [pendantPos] at hv
              change i.val + 2 = j.val + 2 at hv
              exact (Nat.add_right_cancel hv).symm
            subst j
            exact hj.resolve_left (not_not_intro hiU)
        let T := (lastCutsEquiv (s := s)).symm ⟨U.1, U.2, hilast ▸ hiU⟩
        refine ⟨Sum.inr (Sum.inr T), ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          change s + 2 = i.val + 2
          have hv := congrArg Fin.val hilast
          change i.val + 1 = s + 1 at hv
          rw [Nat.add_right_cancel hv]
        · apply Subtype.ext
          change joinCuts (s := 0) T.1 (∅ : Finset (Fin 1)) = U.1
          exact congrArg Subtype.val ((lastCutsEquiv (s := s)).apply_symm_apply
            ⟨U.1, U.2, hilast ▸ hiU⟩)
      · let T := (pendantCutsEquiv i).symm ⟨U.1, U.2, hiU⟩
        refine ⟨Sum.inr (Sum.inl ⟨i, T⟩), ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          change insertPendantCuts i T.1 = U.1
          exact congrArg Subtype.val ((pendantCutsEquiv i).apply_symm_apply
            ⟨U.1, U.2, hiU⟩)

noncomputable def coordinateFibreEquiv :
    CoordinateFibreIndex s ≃ CoordinateActiveIndex s :=
  Equiv.ofBijective coordinateFibreToActive
    ⟨coordinateFibreToActive_injective, coordinateFibreToActive_surjective⟩

noncomputable def coordinatePendantFibreSum (s : ℕ) : (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)), ∑ i : Fin (s + 1),
    ∑ S : LowerAdmissibleCuts s,
      coordinateUpperTerm (pendantPos i).succ π (insertPendantCuts i S.1)

noncomputable def coordinateFirstFibreSum (s : ℕ) : (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)), ∑ S : LowerCutSubsets s,
    coordinateUpperTerm 1 π (firstInsertCuts S.1)

noncomputable def coordinateLastFibreSum (s : ℕ) : (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)), ∑ S : LowerCutSubsets s,
    coordinateUpperTerm (Fin.last (s + 2)) π
      (joinCuts (s := 0) S.1 (∅ : Finset (Fin 1)))

private theorem sum_if_eq_sum_subtype {α M : Type*} [Fintype α]
    [AddCommMonoid M] (P : α → Prop) [DecidablePred P] (f : α → M) :
    (∑ a, if P a then f a else 0) = ∑ a : {a // P a}, f a.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun a => by simp) f

theorem coordinateActiveSum_eq_activeIndexSum :
    coordinateActiveSum s =
      ∑ π : Equiv.Perm (Fin (s + 2)), ∑ q : CoordinateActiveIndex s,
        coordinateUpperTerm q.1.1 π q.1.2.1 := by
  classical
  unfold coordinateActiveSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  have hcuts (p : Fin (s + 3)) :
      (∑ U in admissibleCuts (s + 1),
          if coordinateActive p U then coordinateUpperTerm p π U else 0) =
        ∑ U : UpperAdmissibleCuts s,
          if coordinateActive p U.1 then coordinateUpperTerm p π U.1 else 0 := by
    exact Finset.sum_subtype (admissibleCuts (s + 1)) (fun _ => Iff.rfl) _
  simp_rw [hcuts]
  rw [← Fintype.sum_prod_type']
  exact sum_if_eq_sum_subtype
    (fun q : Fin (s + 3) × UpperAdmissibleCuts s => coordinateActive q.1 q.2.1)
    (fun q => coordinateUpperTerm q.1 π q.2.1)

/-- The active part is exactly the disjoint union of pendant, first-endpoint,
and last-endpoint insertion fibres. -/
theorem coordinateActiveSum_eq_fibreSums :
    coordinateActiveSum s = coordinatePendantFibreSum s +
      coordinateFirstFibreSum s + coordinateLastFibreSum s := by
  classical
  rw [coordinateActiveSum_eq_activeIndexSum]
  unfold coordinatePendantFibreSum coordinateFirstFibreSum coordinateLastFibreSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro π _
  have hreindex := Fintype.sum_equiv (coordinateFibreEquiv (s := s))
    (fun q : CoordinateFibreIndex s =>
      coordinateUpperTerm (coordinateFibreToActive q).1.1 π
        (coordinateFibreToActive q).1.2.1)
    (fun q : CoordinateActiveIndex s => coordinateUpperTerm q.1.1 π q.1.2.1)
    (fun _ => rfl)
  rw [← hreindex]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type,
    coordinateFibreToActive]
  abel

end MaxNN.Caterpillar
