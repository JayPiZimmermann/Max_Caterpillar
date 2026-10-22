import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Instances.Real
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.FieldTheory.Subfield

/-! # Rational coefficients without integration

Version 2 of the coefficient argument.  Let `v` be a finite family of real
functions which is linearly independent on a set `Y` of points at which every
`v i` takes rational values.  The rows `(v i y)_i`, `y ∈ Y`, are rational
vectors.  They span all of `ℚ^ι`: otherwise a nonzero rational functional
would annihilate them, contradicting independence.  Hence each coordinate
functional is a finite rational combination of evaluations, and the
coordinates of any function in the span which is rational on `Y` are
rational.  For continuous functions on `ℝ^N`, independence on all inputs
implies independence on the dense set of rational points.

Nothing here replaces the inverse-Gram prescription (Version 1); by
uniqueness of coordinates the two agree on every basis.
-/

open BigOperators

namespace MaxCaterpillar

/-- The rational numbers inside `ℝ`, as a subfield. -/
noncomputable abbrev ratField : Subfield ℝ := (Rat.castHom ℝ).fieldRange

theorem mem_ratField_iff {t : ℝ} : t ∈ ratField ↔ ∃ q : ℚ, (q : ℝ) = t := by
  rw [RingHom.mem_fieldRange]
  rfl

theorem ratCast_mem_ratField (q : ℚ) : (q : ℝ) ∈ ratField :=
  mem_ratField_iff.mpr ⟨q, rfl⟩

theorem intCast_mem_ratField (z : ℤ) : (z : ℝ) ∈ ratField := by
  have h := ratCast_mem_ratField (z : ℚ)
  rwa [Rat.cast_coe_int] at h

theorem max_mem_ratField {s t : ℝ} (hs : s ∈ ratField) (ht : t ∈ ratField) :
    max s t ∈ ratField := by
  rcases max_choice s t with h | h <;> rw [h] <;> assumption

theorem sum_mem_ratField {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i ∈ s, f i ∈ ratField) : ∑ i in s, f i ∈ ratField :=
  Subfield.sum_mem _ hf

/-- Points with rational coordinates. -/
def ratPoints (N : ℕ) : Set (Fin N → ℝ) := {x | ∀ i, x i ∈ ratField}

theorem dense_ratPoints (N : ℕ) : Dense (ratPoints N) := by
  have h : ratPoints N = Set.pi Set.univ (fun _ : Fin N => Set.range ((↑) : ℚ → ℝ)) := by
    ext x
    simp only [ratPoints, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_range]
    exact forall_congr' fun i => mem_ratField_iff
  rw [h]
  exact dense_pi Set.univ fun _ _ => Rat.denseRange_cast

/-- Continuous functions agreeing on rational points agree everywhere. -/
theorem eq_of_eq_on_ratPoints {N : ℕ} {f g : (Fin N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ x ∈ ratPoints N, f x = g x) :
    f = g :=
  Continuous.ext_on (dense_ratPoints N) hf hg h

section Rows

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]

/-- If the rational rows of an independent family did not span `ℚ^ι`, a
nonzero rational functional would vanish on all of them. -/
theorem rows_span_top (v : ι → X → ℝ) (Y : Set X)
    (hind : ∀ c : ι → ℝ, (∀ y ∈ Y, ∑ i, c i * v i y = 0) → c = 0)
    (row : Y → ι → ℚ) (hrow : ∀ y : Y, ∀ i, ((row y i : ℚ) : ℝ) = v i y) :
    Submodule.span ℚ (Set.range row) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hker⟩ :=
    Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  let c : ι → ℚ := fun i => f (Pi.single i 1)
  have hfc : ∀ w : ι → ℚ, f w = ∑ i, w i * c i := by
    intro w
    rw [LinearMap.pi_apply_eq_sum_univ f w]
    exact Finset.sum_congr rfl fun i _ => by
      rw [smul_eq_mul]
      congr 2
      funext j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
  have hzero : (fun i => (c i : ℝ)) = 0 := by
    apply hind
    intro y hy
    have hk : f (row ⟨y, hy⟩) = 0 :=
      LinearMap.mem_ker.mp (hker (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩))
    rw [hfc] at hk
    have hk' := congrArg (fun q : ℚ => (q : ℝ)) hk
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_zero] at hk'
    rw [← hk']
    exact Finset.sum_congr rfl fun i _ => by rw [hrow ⟨y, hy⟩ i, mul_comm]
  apply hf0
  apply LinearMap.ext
  intro w
  rw [hfc, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi := congrFun hzero i
  simp only [Pi.zero_apply, Rat.cast_eq_zero] at hi
  show w i * f (Pi.single i 1) = 0
  rw [hi, mul_zero]

/-- Coordinates in an independent family are rational whenever the family and
the represented function are rational on the independence set. -/
theorem coeff_mem_ratField (v : ι → X → ℝ) (Y : Set X)
    (hind : ∀ c : ι → ℝ, (∀ y ∈ Y, ∑ i, c i * v i y = 0) → c = 0)
    (hv : ∀ i, ∀ y ∈ Y, v i y ∈ ratField)
    (d : ι → ℝ) (hd : ∀ y ∈ Y, ∑ i, d i * v i y ∈ ratField) (j : ι) :
    d j ∈ ratField := by
  have hq : ∀ y : Y, ∀ i, ∃ q : ℚ, (q : ℝ) = v i y :=
    fun y i => mem_ratField_iff.mp (hv i y.1 y.2)
  choose row hrow using hq
  have htop := rows_span_top v Y hind row hrow
  have hj : (Pi.single j 1 : ι → ℚ) ∈ Submodule.span ℚ (Set.range row) := by
    rw [htop]; trivial
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hj
  -- Evaluate the coordinate functional `w ↦ ∑ i, w i * d i` on both sides.
  have hlhs : ∑ i, (((Pi.single j 1 : ι → ℚ) i : ℚ) : ℝ) * d i = d j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_apply, hij]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [← hlhs, ← ha]
  have hexpand : ∑ i, (((a.sum fun y q => q • row y) i : ℚ) : ℝ) * d i =
      a.sum fun y q => (q : ℝ) * ∑ i, d i * v i y.1 := by
    unfold Finsupp.sum
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sum, Rat.cast_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hrow y i]
    ring
  rw [hexpand]
  exact sum_mem_ratField _ fun y _ =>
    Subfield.mul_mem _ (ratCast_mem_ratField _) (hd y.1 y.2)

end Rows

section Points

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Continuous, independent functions remain independent on rational points. -/
theorem independent_on_ratPoints (v : ι → (Fin N → ℝ) → ℝ) (hc : ∀ i, Continuous (v i))
    (hli : LinearIndependent ℝ v) (c : ι → ℝ)
    (hc0 : ∀ y ∈ ratPoints N, ∑ i, c i * v i y = 0) : c = 0 := by
  have hfun : (fun y => ∑ i, c i * v i y) = fun _ => 0 :=
    eq_of_eq_on_ratPoints
      (continuous_finset_sum _ fun i _ => continuous_const.mul (hc i))
      continuous_const hc0
  funext i
  apply Fintype.linearIndependent_iff.mp hli c
  funext y
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hfun y

/-- Coordinates of a rational-valued function in a continuous independent
rational-valued family are rational. -/
theorem coeff_mem_ratField_of_independent (v : ι → (Fin N → ℝ) → ℝ)
    (hc : ∀ i, Continuous (v i)) (hli : LinearIndependent ℝ v)
    (hv : ∀ i, ∀ y ∈ ratPoints N, v i y ∈ ratField)
    (d : ι → ℝ) (hd : ∀ y ∈ ratPoints N, ∑ i, d i * v i y ∈ ratField) (j : ι) :
    d j ∈ ratField :=
  coeff_mem_ratField v (ratPoints N) (independent_on_ratPoints v hc hli) hv d hd j

end Points

section Span

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A function in the span of a finite continuous family, all rational on
rational points, has rational coefficients in that family.  The coefficients
come from one independent subfamily with the same span. -/
theorem exists_rat_coeff_of_mem_span (v : ι → (Fin N → ℝ) → ℝ)
    (hc : ∀ i, Continuous (v i)) (hv : ∀ i, ∀ y ∈ ratPoints N, v i y ∈ ratField)
    {f : (Fin N → ℝ) → ℝ} (hf : f ∈ Submodule.span ℝ (Set.range v))
    (hfr : ∀ y ∈ ratPoints N, f y ∈ ratField) :
    ∃ c : ι → ℝ, (∀ i, c i ∈ ratField) ∧ ∀ x, f x = ∑ i, c i * v i x := by
  classical
  obtain ⟨b, hbv, hspan, hli⟩ := exists_linearIndependent ℝ (Set.range v)
  have hbfin : b.Finite := (Set.finite_range v).subset hbv
  haveI : Fintype b := hbfin.fintype
  -- pick one index for every chosen function
  have hpick : ∀ g : b, ∃ i, v i = g.1 := fun g => hbv g.2
  choose idx hidx using hpick
  have hidx_inj : Function.Injective idx := by
    intro g h hgh
    apply Subtype.ext
    rw [← hidx g, ← hidx h, hgh]
  rw [← hspan] at hf
  have hrange : Set.range (fun g : b => g.1) = b := Subtype.range_coe
  rw [← hrange, mem_span_range_iff_exists_fun] at hf
  obtain ⟨d, hd⟩ := hf
  have hdx : ∀ x, f x = ∑ g : b, d g * g.1 x := by
    intro x
    rw [← hd]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hrat : ∀ g, d g ∈ ratField := by
    apply coeff_mem_ratField_of_independent (fun g : b => g.1)
    · intro g
      rw [← hidx g]
      exact hc _
    · exact hli
    · intro g y hy
      rw [← hidx g]
      exact hv _ y hy
    · intro y hy
      rw [← hdx y]
      exact hfr y hy
  refine ⟨fun i => if h : ∃ g, idx g = i then d (Classical.choose h) else 0, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with h
    · exact hrat _
    · exact Subfield.zero_mem _
  · intro x
    rw [hdx x]
    have himage : ∑ i, (if h : ∃ g, idx g = i then d (Classical.choose h) else 0) * v i x =
        ∑ i in Finset.univ.image idx,
          (if h : ∃ g, idx g = i then d (Classical.choose h) else 0) * v i x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hn : ¬ ∃ g, idx g = i := by
        rintro ⟨g, rfl⟩
        exact hi (Finset.mem_image_of_mem _ (Finset.mem_univ g))
      rw [dif_neg hn, zero_mul]
    rw [himage, Finset.sum_image fun g _ h _ hgh => hidx_inj hgh]
    apply Finset.sum_congr rfl
    intro g _
    have hex : ∃ g', idx g' = idx g := ⟨g, rfl⟩
    rw [dif_pos hex, hidx_inj (Classical.choose_spec hex), hidx g]

end Span

end MaxCaterpillar
