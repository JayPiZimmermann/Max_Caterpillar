import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Model

/-! Exact directional germs of finite affine shallow functions are shallow. -/
set_option autoImplicit false

namespace MaxCaterpillar.Max5Optimal.ConvexCores
open BigOperators Filter Topology Frontier
open Frontier.RandomRestriction.NormalizedNetwork

variable {N m : ℕ}

namespace ExactTangent

variable {f g : Point N → ℝ} {q : Point N} {e : Fin m ↪ Fin N}
    {Df Dg : Point m → ℝ}

theorem add (hf : ExactTangent f q e Df) (hg : ExactTangent g q e Dg) :
    ExactTangent (fun x => f x + g x) q e (fun x => Df x + Dg x) := by
  intro x
  filter_upwards [hf x, hg x] with ε hfε hgε
  simp only [hfε, hgε]
  ring

theorem smul (c : ℝ) (hf : ExactTangent f q e Df) :
    ExactTangent (fun x => c * f x) q e (fun x => c * Df x) := by
  intro x
  filter_upwards [hf x] with ε hε
  simp only [hε]
  ring

theorem relu (hf : ExactTangent f q e Df) :
    ExactTangent (fun x => MaxCaterpillar.relu (f x)) q e
      (fun x => pick (f q) (Df x) (MaxCaterpillar.relu (Df x))) := by
  intro x
  filter_upwards [hf x, eventually_relu_direction (f q) (Df x)] with ε hfε hrε
  simpa only [hfε] using hrε

theorem sum {ι : Type*} [Fintype ι] (f : ι → Point N → ℝ)
    (D : ι → Point m → ℝ) (h : ∀ i, ExactTangent (f i) q e (D i)) :
    ExactTangent (fun x => ∑ i, f i x) q e (fun x => ∑ i, D i x) := by
  intro x
  filter_upwards [Filter.eventually_all.mpr (fun i => h i x)] with ε hε
  simp only [hε, Finset.sum_add_distrib, Finset.mul_sum]

end ExactTangent

theorem IsShallow.exists_tangent {f : Point N → ℝ} (hf : IsShallow f)
    (q : Point N) (e : Fin m ↪ Fin N) :
    ∃ D : Point m → ℝ, IsShallow D ∧ ExactTangent f q e D := by
  induction hf with
  | affine a b =>
      refine ⟨fun x => lin (restrict e a) x, ?_, ?_⟩
      · simpa only [add_zero] using IsShallow.affine (restrict e a) 0
      · intro x
        exact Filter.eventually_of_forall fun ε => by
          change lin a (q + ε • lift e x) + b =
            lin a q + b + ε * lin (restrict e a) x
          rw [lin_add_right, lin_smul_right, lin_lift]
          ring
  | hinge a b =>
      refine ⟨fun x => pick (lin a q + b) (lin (restrict e a) x)
        (relu (lin (restrict e a) x)), ?_, ?_⟩
      · by_cases hp : 0 < lin a q + b
        · simpa only [pick, if_pos hp, add_zero] using IsShallow.affine (restrict e a) 0
        · by_cases hn : lin a q + b < 0
          · simpa only [pick, if_neg hp, if_pos hn, lin_zero_left, zero_add] using
              IsShallow.affine (0 : Point m) 0
          · simpa only [pick, if_neg hp, if_neg hn, add_zero] using
              IsShallow.hinge (restrict e a) 0
      · intro x
        filter_upwards [eventually_relu_direction (lin a q + b) (lin (restrict e a) x)]
          with ε hε
        rw [lin_add_right, lin_smul_right, lin_lift]
        convert hε using 1 <;> congr 1 <;> ring
  | add hf hg ihf ihg =>
      obtain ⟨Df, hDf, htf⟩ := ihf
      obtain ⟨Dg, hDg, htg⟩ := ihg
      refine ⟨fun x => Df x + Dg x, hDf.add hDg, ?_⟩
      intro x
      filter_upwards [htf x, htg x] with ε hfε hgε
      simp only [hfε, hgε]
      ring
  | smul c hf ih =>
      obtain ⟨D, hD, ht⟩ := ih
      refine ⟨fun x => c * D x, IsShallow.smul c hD, ?_⟩
      intro x
      filter_upwards [ht x] with ε hε
      simp only [hε]
      ring

#check @IsShallow.exists_tangent
#print axioms IsShallow.exists_tangent
#print axioms ExactTangent.add
#print axioms ExactTangent.smul
#print axioms ExactTangent.relu
#print axioms ExactTangent.sum

end MaxCaterpillar.Max5Optimal.ConvexCores
