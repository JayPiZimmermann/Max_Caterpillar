import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Anchored decomposition for arbitrary leaf functions

The functions are completely arbitrary. The proof is finite Möbius inversion,
not a polynomial reduction, continuity argument, or check on a real grid.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

variable {L : Type*} [DecidableEq L]

/-- Keep the coordinates in `T` and anchor all others at zero. -/
noncomputable def zeroOutside (T : Finset L) (z : L → ℝ) : L → ℝ :=
  fun l => if l ∈ T then z l else 0

/-- Select the first or second value of each leaf according to `P`. -/
noncomputable def mixed (P : Finset L) (v v' : L → ℝ) : L → ℝ :=
  fun l => if l ∈ P then v l else v' l

/-- The finite anchored difference of an arbitrary function of subsets. -/
noncomputable def anchoredDifference (S : Finset L) (f : Finset L → ℝ) : ℝ :=
  ∑ T in S.powerset, (-1 : ℝ) ^ (S \ T).card * f T

lemma anchoredDifference_insert (S : Finset L) (a : L) (ha : a ∉ S)
    (f : Finset L → ℝ) :
    anchoredDifference (insert a S) f =
      anchoredDifference S (fun T => f (insert a T) - f T) := by
  unfold anchoredDifference
  rw [Finset.sum_powerset_insert ha,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have haT : a ∉ T := fun h => ha ((Finset.mem_powerset.mp hT) h)
  have haD : a ∉ S \ T := fun h => ha (Finset.mem_sdiff.mp h).1
  rw [Finset.insert_sdiff_of_not_mem S haT,Finset.card_insert_of_not_mem haD,
    Finset.insert_sdiff_insert,Finset.sdiff_insert_of_not_mem ha,pow_succ]
  ring

/-- Finite Möbius inversion, valid for an arbitrary subset-indexed function. -/
theorem sum_anchoredDifference (U : Finset L) (f : Finset L → ℝ) :
    (∑ S in U.powerset, anchoredDifference S f) = f U := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp [anchoredDifference]
  | @insert a U ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have he : (∑ S in U.powerset,anchoredDifference (insert a S) f) =
        ∑ S in U.powerset,anchoredDifference S (fun T => f (insert a T)-f T) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact anchoredDifference_insert S a
        (fun h => ha ((Finset.mem_powerset.mp hS) h)) f
    rw [he,ih,ih]
    ring

variable [Fintype L]

/-- Jensen's anchored component, with its two finite sums in the stated order. -/
noncomputable def component (Ψ : Finset L → (L → ℝ) → ℝ)
    (S A : Finset L) (z : L → ℝ) : ℝ :=
  ∑ T in S.powerset, (-1 : ℝ) ^ (S \ T).card *
    ∑ P in (Finset.univ : Finset L).powerset.filter (fun P => P ∩ S = A),
      Ψ P (zeroOutside T z)

@[simp] theorem zeroOutside_univ (z : L → ℝ) :
    zeroOutside Finset.univ z = z := by
  funext l
  simp [zeroOutside]

@[simp] theorem zeroOutside_empty (z : L → ℝ) :
    zeroOutside ∅ z = 0 := by
  funext l
  simp [zeroOutside]

lemma zeroOutside_mixed_inter (S T P : Finset L) (hT : T ⊆ S)
    (v v' : L → ℝ) :
    zeroOutside T (mixed (P ∩ S) v v') = zeroOutside T (mixed P v v') := by
  funext l
  by_cases hlT : l ∈ T
  · have hlS := hT hlT
    simp [zeroOutside,mixed,hlT,hlS]
  · simp [zeroOutside,hlT]

lemma component_eq_fiber (Ψ : Finset L → (L → ℝ) → ℝ)
    (S A : Finset L) (z : L → ℝ) :
    component Ψ S A z =
      ∑ P in (Finset.univ : Finset L).powerset.filter (fun P => P ∩ S=A),
        anchoredDifference S (fun T => Ψ P (zeroOutside T z)) := by
  unfold component anchoredDifference
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Summing the compatible leaf choices reassembles every subset-indexed
function exactly once, with no regularity hypothesis on those functions. -/
theorem sum_components_eq (Ψ : Finset L → (L → ℝ) → ℝ)
    (S : Finset L) (v v' : L → ℝ) :
    (∑ A in S.powerset,component Ψ S A (mixed A v v')) =
      ∑ P in (Finset.univ : Finset L).powerset,
        anchoredDifference S (fun T => Ψ P (zeroOutside T (mixed P v v'))) := by
  simp_rw [component_eq_fiber]
  calc
    (∑ A in S.powerset,
        ∑ P in (Finset.univ : Finset L).powerset.filter (fun P => P ∩ S=A),
          anchoredDifference S (fun T => Ψ P (zeroOutside T (mixed A v v')))) =
      ∑ A in S.powerset,
        ∑ P in (Finset.univ : Finset L).powerset.filter (fun P => P ∩ S=A),
          anchoredDifference S (fun T => Ψ P (zeroOutside T (mixed P v v'))) := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro P hP
        unfold anchoredDifference
        apply Finset.sum_congr rfl
        intro T hT
        have hPA := (Finset.mem_filter.mp hP).2
        dsimp only
        rw [← hPA,zeroOutside_mixed_inter S T P (Finset.mem_powerset.mp hT)]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset L).powerset) (t := S.powerset)
      (g := fun P : Finset L => P ∩ S)
      (fun P _ => Finset.mem_powerset.mpr (Finset.inter_subset_right P S)) _

/-- Exact anchored ANOVA identity on all real inputs, for arbitrary functions. -/
theorem anchored_sum_decomposition (Ψ : Finset L → (L → ℝ) → ℝ)
    (v v' : L → ℝ) :
    (∑ P in (Finset.univ : Finset L).powerset,Ψ P (mixed P v v')) =
      ∑ S in (Finset.univ : Finset L).powerset,
        ∑ A in S.powerset,component Ψ S A (mixed A v v') := by
  symm
  simp_rw [sum_components_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P _
  rw [sum_anchoredDifference,zeroOutside_univ]

/-- Jensen's anchored-decomposition implication (Lemma 23), including the
empty component through the explicit zero-at-anchor hypothesis. -/
theorem anchored_sum_eq_zero (Ψ : Finset L → (L → ℝ) → ℝ)
    (hzero : ∀ P,Ψ P 0=0)
    (hcomponent : ∀ S A : Finset L,S.Nonempty → A ⊆ S →
      ∀ z : L → ℝ,component Ψ S A z=0) (v v' : L → ℝ) :
    (∑ P in (Finset.univ : Finset L).powerset,Ψ P (mixed P v v')) = 0 := by
  rw [anchored_sum_decomposition]
  apply Finset.sum_eq_zero
  intro S _
  apply Finset.sum_eq_zero
  intro A hA
  by_cases hS : S=∅
  · subst S
    have hAe : A=∅ := Finset.subset_empty.mp (Finset.mem_powerset.mp hA)
    subst A
    simp [component,hzero]
  · exact hcomponent S A (Finset.nonempty_iff_ne_empty.mpr hS)
      (Finset.mem_powerset.mp hA) (mixed A v v')

#print axioms sum_anchoredDifference
#print axioms anchored_sum_decomposition
#print axioms anchored_sum_eq_zero
end MaxCaterpillar.Frontier.StarCertificate
