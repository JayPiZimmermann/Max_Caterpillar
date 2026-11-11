import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointNetwork
import MaxCaterpillar.Fiber.Count65.Paired.BaselineWeighted
import MaxCaterpillar.Fiber.Count65.Paired.SwitchingPath

/-! # The actual residual after any target-comparison cluster is a weighted baseline

This bridges an all-input exact physical network to the baseline attachment
hypothesis. It uniformly covers one comparison, two merged orientations, and
any larger target-knot cluster before dormant slots are reused.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier

lemma paired_zeroBias_eval {m : ℕ} (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hb : net.HasZeroBiases)
    (x : Point 4) : net.eval x=∑ k, net.w₃ k*relu (endpointForm U (net.W₂ k) x) := by
  rcases hb with ⟨h1,h2,h3⟩
  simp only [Network.eval,hU,h1,h2,h3,Pi.zero_apply,add_zero,endpointForm,endpointFeature]

lemma weightedTarget_endpointForm (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (x : Point 4) :
    BaselineWeighted.weightedTarget s x=endpointForm U (baselineRow U) x+
      s*endpointForm U (comparisonRow U) x := by
  rw [baselineRow_form U hU,comparisonRow_form U hU]
  have hA := relu_sub_add (x 1) (x 0)
  have hB := relu_sub_add (x 3) (x 2)
  rw [max_comm (x 1) (x 0)] at hA
  rw [max_comm (x 3) (x 2)] at hB
  unfold BaselineWeighted.weightedTarget
  rw [hA,hB]
  ring

/-- A finite target-comparison cluster with total jump one leaves exactly
L_s, where s is its total negative-orientation readout coefficient. -/
theorem comparison_cluster_baseline_fit {m : ℕ} (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U≠0) (hU : net.W₁=pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x, net.eval x=Maximum 4 x)
    (C : Finset (Fin m)) (flip : Fin m → Bool)
    (hnatural : ∀ i∈C, ∀ x, endpointForm U (net.W₂ i) x=
      if flip i then -endpointForm U (comparisonRow U) x else endpointForm U (comparisonRow U) x)
    (hweight : (∑ i in C, net.w₃ i)=1) :
    ∀ x, (∑ i in Finset.univ\C, net.w₃ i*relu (endpointForm U (net.W₂ i) x))=
      BaselineWeighted.weightedTarget (∑ i in C, net.w₃ i*orientationIndicator (flip i)) x := by
  classical
  intro x
  let D := endpointForm U (comparisonRow U) x
  let B := endpointForm U (baselineRow U) x
  let s := ∑ i in C, net.w₃ i*orientationIndicator (flip i)
  have hcomparison : (∑ i in C, net.w₃ i*relu (endpointForm U (net.W₂ i) x))=
      relu D-s*D := by
    have he : ∀ i∈C, relu (endpointForm U (net.W₂ i) x)=
        relu D-orientationIndicator (flip i)*D := by
      intro i hi
      rw [hnatural i hi x]
      cases hflip : flip i
      · simp [orientationIndicator,hflip,D]
      · simp only [hflip,if_true,orientationIndicator,one_mul]
        have hh := relu_sub_relu_neg D
        linarith only [hh]
    calc
      _ = ∑ i in C, net.w₃ i*(relu D-orientationIndicator (flip i)*D) :=
        Finset.sum_congr rfl (fun i hi => congrArg (fun z => net.w₃ i*z) (he i hi))
      _ = (∑ i in C,net.w₃ i)*relu D-s*D := by
        dsimp only [s]
        simp only [Finset.sum_mul,Finset.sum_sub_distrib,mul_sub,mul_assoc]
      _ = relu D-s*D := by rw [hweight,one_mul]
  have hs := Finset.sum_sdiff (Finset.subset_univ C)
    (f := fun i => net.w₃ i*relu (endpointForm U (net.W₂ i) x))
  have ht := hnet x
  rw [paired_zeroBias_eval net U hU hb x] at ht
  have hm := (pairedMinimalNet_eval U hdet x).symm
  rw [pairedMinimalNet_eval_formula] at hm
  rw [weightedTarget_endpointForm U hdet]
  change (∑ i in Finset.univ\C, net.w₃ i*relu (endpointForm U (net.W₂ i) x))=B+s*D
  rw [hcomparison] at hs
  change Maximum 4 x=B+relu D at hm
  linarith only [hs,ht,hm]

end MaxCaterpillar.Fiber.Count65.Paired
