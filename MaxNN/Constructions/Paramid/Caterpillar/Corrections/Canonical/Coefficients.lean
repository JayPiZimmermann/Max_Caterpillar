import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Canonical.Average
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Canonical.FiberCompiler

/-!
# Literal coefficients from the canonical Gram average

The coefficient of a dictionary function is the average of its inverse-Gram
coefficient over every basis subset.  For a tagged family, equal functions
split that coefficient equally over their finite fiber.  Thus the resulting
coefficient of every tag is given by one finite formula, even when the family
contains duplicates.
-/

open BigOperators MeasureTheory

namespace MaxNN.Caterpillar.Corrections.Canonical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] [Nontrivial E]

noncomputable section

local instance : DecidableEq (E → ℝ) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The coefficient contributed by one basis subset, extended by zero away
from that subset. -/
def basisCoeff (S : Finset (E → ℝ)) (f g : E → ℝ) : ℝ :=
  if hg : g ∈ S then gramCoeff (fun h : ↑S ↦ h.1) f ⟨g, hg⟩ else 0

theorem basisExpansion_eq_sum_basisCoeff {D S : Finset (E → ℝ)}
    (hSD : S ⊆ D) (f : E → ℝ) (x : E) :
    basisExpansion S f x = ∑ g in D, basisCoeff S f g * g x := by
  unfold basisExpansion lincomb
  calc
    (∑ g : ↑S, gramCoeff (fun h : ↑S ↦ h.1) f g * g.1 x) =
        ∑ g in S, basisCoeff S f g * g x := by
      rw [← Finset.sum_coe_sort S]
      apply Finset.sum_congr rfl
      intro g _
      simp only [basisCoeff, g.2, dite_true]
    _ = ∑ g in D, basisCoeff S f g * g x := by
      apply Finset.sum_subset hSD
      intro g _ hg
      simp only [basisCoeff, hg, dite_false, zero_mul]

/-- The coefficient of one distinct dictionary function. -/
def canonicalCoeff (D : Finset (E → ℝ)) (f g : E → ℝ) : ℝ :=
  ((basisSubsets D).card : ℝ)⁻¹ *
    ∑ S in basisSubsets D, basisCoeff S f g

theorem basisAverage_eq_sum_canonicalCoeff (D : Finset (E → ℝ))
    (f : E → ℝ) (x : E) :
    basisAverage D f x = ∑ g in D, canonicalCoeff D f g * g x := by
  unfold basisAverage canonicalCoeff
  rw [Finset.sum_congr rfl fun S hS ↦
    basisExpansion_eq_sum_basisCoeff (mem_basisSubsets_iff.mp hS).1 f x]
  let a : ℝ := ((basisSubsets D).card : ℝ)⁻¹
  change a * (∑ S in basisSubsets D, ∑ g in D, basisCoeff S f g * g x) =
    ∑ g in D, (a * ∑ S in basisSubsets D, basisCoeff S f g) * g x
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem sum_canonicalCoeff_eq {D : Finset (E → ℝ)}
    (hD : ∀ g ∈ D, IsPosHomContinuous g)
    {f : E → ℝ} (hf : f ∈ Submodule.span ℝ (↑D : Set (E → ℝ))) (x : E) :
    ∑ g in D, canonicalCoeff D f g * g x = f x := by
  rw [← basisAverage_eq_sum_canonicalCoeff]
  exact congrFun (basisAverage_eq D hD hf) x

section Tagged

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The distinct-function dictionary underlying a tagged finite family. -/
def taggedDictionary (v : I → E → ℝ) : Finset (E → ℝ) :=
  Finset.univ.image v

/-- Tags whose functions equal `g`. -/
def taggedFiber (v : I → E → ℝ) (g : E → ℝ) : Finset I :=
  finiteFiber v g

/-- The canonical coefficient of a tag.  Duplicate tags split the coefficient
of their common function equally. -/
def taggedCoeff (v : I → E → ℝ) (f : E → ℝ) (i : I) : ℝ :=
  canonicalCoeff (taggedDictionary v) f (v i) /
    ((taggedFiber v (v i)).card : ℝ)

theorem taggedFiber_nonempty (v : I → E → ℝ) (i : I) :
    (taggedFiber v (v i)).Nonempty := by
  apply finiteFiber_nonempty_of_mem_image
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem sum_taggedCoeff_eq_sum_canonicalCoeff (v : I → E → ℝ)
    (f : E → ℝ) (x : E) :
    ∑ i, taggedCoeff v f i * v i x =
      ∑ g in taggedDictionary v, canonicalCoeff (taggedDictionary v) f g * g x := by
  simpa only [taggedCoeff, taggedFiber, taggedDictionary] using
    (sum_finiteFiber_average_mul_eq_sum_image v
      (canonicalCoeff (taggedDictionary v) f) (fun g ↦ g x))

theorem sum_taggedCoeff_eq (v : I → E → ℝ)
    (hv : ∀ i, IsPosHomContinuous (v i))
    {f : E → ℝ}
    (hf : f ∈ Submodule.span ℝ (↑(taggedDictionary v) : Set (E → ℝ))) (x : E) :
    ∑ i, taggedCoeff v f i * v i x = f x := by
  rw [sum_taggedCoeff_eq_sum_canonicalCoeff]
  apply sum_canonicalCoeff_eq
  · intro g hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    exact hv i
  · exact hf

end Tagged

end

end MaxNN.Caterpillar.Corrections.Canonical
