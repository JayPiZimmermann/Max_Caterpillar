import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Canonical.Gram

/-!
# Canonical coefficients by averaging all Gram bases

For a finite dictionary of functions, take every linearly independent subset
with the same span.  Each subset has an explicit inverse-Gram expansion.  Their
finite average is canonical: no basis, ordering, or coefficient witness is
selected.
-/

open BigOperators MeasureTheory

namespace MaxNN.Caterpillar.Corrections.Canonical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] [Nontrivial E]

noncomputable section

local instance : DecidableEq (E → ℝ) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The independent subsets having exactly the span of `D`. -/
def basisSubsets (D : Finset (E → ℝ)) : Finset (Finset (E → ℝ)) :=
  D.powerset.filter fun S ↦
    LinearIndependent ℝ (fun g : ↑S ↦ g.1) ∧
      Submodule.span ℝ (↑S : Set (E → ℝ)) =
        Submodule.span ℝ (↑D : Set (E → ℝ))

theorem mem_basisSubsets_iff {D S : Finset (E → ℝ)} :
    S ∈ basisSubsets D ↔
      S ⊆ D ∧ LinearIndependent ℝ (fun g : ↑S ↦ g.1) ∧
        Submodule.span ℝ (↑S : Set (E → ℝ)) =
          Submodule.span ℝ (↑D : Set (E → ℝ)) := by
  simp only [basisSubsets, Finset.mem_filter, Finset.mem_powerset]

/-- There is at least one basis subset.  This is used only to prove that the
denominator in the symmetric average is nonzero; the definition never chooses
one of these subsets. -/
theorem basisSubsets_nonempty (D : Finset (E → ℝ)) :
    (basisSubsets D).Nonempty := by
  obtain ⟨b, hbD, hspan, hli⟩ := exists_linearIndependent ℝ (↑D : Set (E → ℝ))
  have hbfin : b.Finite := D.finite_toSet.subset hbD
  let S : Finset (E → ℝ) := hbfin.toFinset
  have hSb : (↑S : Set (E → ℝ)) = b := hbfin.coe_toFinset
  refine ⟨S, mem_basisSubsets_iff.mpr ⟨?_, ?_, ?_⟩⟩
  · intro g hg
    exact hbD (hSb ▸ (Finset.mem_coe.mpr hg))
  · change LinearIndependent ℝ ((↑) : (↑S : Set (E → ℝ)) → E → ℝ)
    rw [hSb]
    exact hli
  · rw [hSb]
    exact hspan

/-- The exact inverse-Gram expansion attached to one finite subset. -/
def basisExpansion (S : Finset (E → ℝ)) (f : E → ℝ) : E → ℝ :=
  lincomb (fun g : ↑S ↦ g.1) (gramCoeff (fun g : ↑S ↦ g.1) f)

theorem basisExpansion_eq {D S : Finset (E → ℝ)}
    (hS : S ∈ basisSubsets D) (hD : ∀ g ∈ D, IsPosHomContinuous g)
    {f : E → ℝ} (hf : f ∈ Submodule.span ℝ (↑D : Set (E → ℝ))) :
    basisExpansion S f = f := by
  obtain ⟨hSD, hli, hspan⟩ := mem_basisSubsets_iff.mp hS
  have hv : ∀ g : ↑S, IsPosHomContinuous g.1 :=
    fun g ↦ hD g.1 (hSD g.2)
  apply lincomb_gramCoeff_eq (fun g : ↑S ↦ g.1) hv hli
  rw [← hspan] at hf
  have hrange : Set.range (fun g : ↑S ↦ g.1) = (↑S : Set (E → ℝ)) := by
    ext g
    simp
  rw [← hrange, mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, ?_⟩
  funext x
  have hcx := congrFun hc.symm x
  simpa only [lincomb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcx

/-- The permutation-invariant average over every basis subset. -/
def basisAverage (D : Finset (E → ℝ)) (f : E → ℝ) : E → ℝ :=
  fun x ↦ ((basisSubsets D).card : ℝ)⁻¹ *
    ∑ S in basisSubsets D, basisExpansion S f x

theorem basisAverage_eq (D : Finset (E → ℝ))
    (hD : ∀ g ∈ D, IsPosHomContinuous g)
    {f : E → ℝ} (hf : f ∈ Submodule.span ℝ (↑D : Set (E → ℝ))) :
    basisAverage D f = f := by
  funext x
  unfold basisAverage
  rw [Finset.sum_congr rfl fun S hS ↦ congrFun (basisExpansion_eq hS hD hf) x,
    Finset.sum_const, nsmul_eq_mul]
  have hcard : ((basisSubsets D).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr (basisSubsets_nonempty D)))
  field_simp
  ring

end

end MaxNN.Caterpillar.Corrections.Canonical
