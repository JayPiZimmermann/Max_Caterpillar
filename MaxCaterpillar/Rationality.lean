import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Instances.Real
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.FieldTheory.Subfield

/-! # Rational coefficients by a ℚ-linear projection

Let `π : ℝ → ℚ` be a ℚ-linear map with `π q = q` on `ℚ` (a left inverse of the
inclusion `ℚ → ℝ`). If `f = ∑ dᵢ vᵢ` with real `dᵢ`, and `f` and every `vᵢ` are
rational at rational points, applying `π` to the identity at a rational point
`y` gives `f y = ∑ π(dᵢ) vᵢ y`. Both sides are continuous and agree on the dense
set `ℚ^N`, hence everywhere (`exists_rat_coeff_of_mem_span`). No basis or
independence argument is needed, and the expansion keeps its support.
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

/-- A function in the span of a finite continuous family, all rational on
rational points, has rational coefficients in that family. Proof: apply a
ℚ-linear projection `ℝ → ℚ` to any real expansion at the rational points. -/
theorem exists_rat_coeff_of_mem_span {N : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → (Fin N → ℝ) → ℝ) (hc : ∀ i, Continuous (v i))
    (hv : ∀ i, ∀ y ∈ ratPoints N, v i y ∈ ratField)
    {f : (Fin N → ℝ) → ℝ} (hf : f ∈ Submodule.span ℝ (Set.range v))
    (hfr : ∀ y ∈ ratPoints N, f y ∈ ratField) :
    ∃ c : ι → ℝ, (∀ i, c i ∈ ratField) ∧ ∀ x, f x = ∑ i, c i * v i x := by
  obtain ⟨d, hd⟩ := (mem_span_range_iff_exists_fun ℝ).mp hf
  have hfx : ∀ x, f x = ∑ i, d i * v i x := fun x => by simp [← hd, Finset.sum_apply]
  obtain ⟨π, hπ⟩ := (Algebra.linearMap ℚ ℝ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℝ).injective)
  have hπq : ∀ q : ℚ, π q = q := fun q => by simpa using LinearMap.congr_fun hπ q
  refine ⟨fun i => (π (d i) : ℝ), fun i => ratCast_mem_ratField _, fun x => ?_⟩
  refine congrFun (eq_of_eq_on_ratPoints (f := f) (g := fun x => ∑ i, (π (d i) : ℝ) * v i x) ?_ ?_ fun y hy => ?_) x
  · simp only [funext hfx]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (hc i)
  · exact continuous_finset_sum _ fun i _ => continuous_const.mul (hc i)
  choose q hq using fun i => mem_ratField_iff.mp (hv i y hy)
  obtain ⟨p, hp⟩ := mem_ratField_iff.mp (hfr y hy)
  have h1 : ((p : ℚ) : ℝ) = ∑ i, q i • d i := by
    rw [hp, hfx]
    exact Finset.sum_congr rfl fun i _ => by rw [Rat.smul_def, hq, mul_comm]
  have h2 := congrArg π h1
  rw [hπq, map_sum] at h2
  simp only [map_smul, smul_eq_mul] at h2
  rw [← hp, h2]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by rw [hq, mul_comm]

end MaxCaterpillar
