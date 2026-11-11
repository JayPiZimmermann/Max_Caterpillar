import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Directional
import Mathlib.Analysis.Convex.Function

/-! Finite affine shallow functions, without a fixed common dictionary.
The constructors are exactly finite affine combinations of affine ReLUs.
No convexity or representation obstruction is built into this definition. -/

set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.ConvexCores
open BigOperators Filter Topology Frontier
open Frontier.RandomRestriction.NormalizedNetwork

inductive IsShallow {N : ℕ} : (Point N → ℝ) → Prop
  | affine (a : Point N) (b : ℝ) : IsShallow (fun x => lin a x + b)
  | hinge (a : Point N) (b : ℝ) : IsShallow (fun x => relu (lin a x + b))
  | add {f g : Point N → ℝ} : IsShallow f → IsShallow g →
      IsShallow (fun x => f x + g x)
  | smul (c : ℝ) {f : Point N → ℝ} : IsShallow f →
      IsShallow (fun x => c * f x)

namespace IsShallow
variable {N : ℕ} {f g : Point N → ℝ}

theorem congr (hf : IsShallow f) (h : ∀ x, f x = g x) : IsShallow g := by
  have he : f = g := funext h
  exact he ▸ hf

theorem zero : IsShallow (fun _ : Point N => (0 : ℝ)) :=
  (affine 0 0).congr (fun _ => by simp [lin_zero_left])

theorem neg (hf : IsShallow f) : IsShallow (fun x => -f x) :=
  (smul (-1) hf).congr (fun _ => by ring)

theorem sub (hf : IsShallow f) (hg : IsShallow g) :
    IsShallow (fun x => f x - g x) :=
  (hf.add hg.neg).congr (fun _ => by ring)

theorem sum {ι : Type*} (s : Finset ι) (f : ι → Point N → ℝ)
    (hf : ∀ i ∈ s, IsShallow (f i)) : IsShallow (fun x => ∑ i in s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (N := N))
  | @insert a s ha ih =>
      have hsum := (hf a (by simp)).add
        (ih (fun i hi => hf i (by simp [hi])))
      exact hsum.congr (fun x => by simp [Finset.sum_insert, ha])

theorem locOddLin (hf : IsShallow f) (q : Point N) : LocOddLin f q := by
  induction hf with
  | affine a b => exact ((locAff_lin a q).add (locAff_const b q)).locOddLin
  | hinge a b => exact ((locAff_lin a q).add (locAff_const b q)).relu_locOddLin
  | add hf hg ihf ihg => exact ihf.add ihg
  | smul c hf ih => exact ih.const_mul c

theorem continuous (hf : IsShallow f) : Continuous f := by
  have hlin (a : Point N) : Continuous (lin a) := by
    unfold lin
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)
  induction hf with
  | affine a b => exact (hlin a).add continuous_const
  | hinge a b => exact continuous_relu.comp ((hlin a).add continuous_const)
  | add hf hg ihf ihg => exact ihf.add ihg
  | smul c hf ih => exact continuous_const.mul ih

theorem raw {m : ℕ} (a : Point N) (b : ℝ) (A : Fin m → Point N)
    (β c : Fin m → ℝ) :
    IsShallow (fun x => lin a x + b + ∑ j, c j * relu (lin (A j) x + β j)) :=
  (affine a b).add (sum Finset.univ _ (fun j _ => smul (c j) (hinge (A j) (β j))))

end IsShallow

def ExactTangent {N m : ℕ} (f : Point N → ℝ) (q : Point N)
    (e : Fin m ↪ Fin N) (D : Point m → ℝ) : Prop :=
  ∀ x, ∀ᶠ ε in 𝓝[>] (0 : ℝ), f (q + ε • lift e x) = f q + ε * D x

/-- An actual finite shallow-remainder representation, with global convexity
as its explicit additional hypothesis. Weights may have either sign. -/
structure ConvexRepresentation (N : ℕ) [NeZero N] (κ : Type*) [Fintype κ] where
  remainder : Point N → ℝ
  core : κ → Point N → ℝ
  weight : κ → ℝ
  shallow_remainder : IsShallow remainder
  shallow_core : ∀ k, IsShallow (core k)
  convex_core : ∀ k, ConvexOn ℝ Set.univ (core k)
  computes : ∀ x, remainder x + ∑ k, weight k * relu (core k x) = Maximum N x

theorem not_shallow_max {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    ¬ IsShallow (Maximum N) := by
  intro h
  exact not_locOddLin_max (0 : Point N) Finset.univ (by simpa using hN)
    (fun _ _ => rfl) (fun i hi => False.elim (hi (Finset.mem_univ i)))
    (h.locOddLin 0)

#check @IsShallow.raw
#check @not_shallow_max
#print axioms not_shallow_max
end MaxCaterpillar.Max5Optimal.ConvexCores
