import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Basic
import MaxCaterpillar.Fiber.Count65.Paired.BaselineWeighted
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointNetwork

set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
open BigOperators Absorption Frontier QuadrantGroups
variable {N m k : ℕ} [NeZero N]

theorem signedNet_change_carrier (a : Network N m k) (S : Finset (Fin k))
    (p n : Fin k) (L M : Fin m → ℝ) (η μ : ℝ)
    (hLM : ∀ x,preact a.W₁ a.b₁ M μ x=preact a.W₁ a.b₁ L η x)
    (ha : ∀ x,(signedNet a S p n L η).eval x=Maximum N x) :
    JoinedIn (ExactSet N m k) (signedNet a S p n L η) (signedNet a S p n M μ) := by
  let b := signedNet a S p n L η
  have hh : ∀ i,b.w₃ i≠0 → ∀ x,
      preact b.W₁ b.b₁ (signedChordRows a S p n M i) (signedChordBiases a S p n μ i) x=
      preact b.W₁ b.b₁ (b.W₂ i) (b.b₂ i) x := by
    intro i _hi x
    by_cases hip : i=p
    · simpa only [b,signedNet,signedChordRows,signedChordBiases,if_pos hip] using hLM x
    · by_cases hin : i=n
      · simp only [b,signedNet,signedChordRows,signedChordBiases,if_neg hip,if_pos hin]
        change preact a.W₁ a.b₁ (fun j=> -M j) (-μ) x=
          preact a.W₁ a.b₁ (fun j=> -L j) (-η) x
        rw [preact_neg,preact_neg,hLM x]
      · by_cases hi : i∈S <;>
          simp only [b,signedNet,signedChordRows,signedChordBiases,if_neg hip,if_neg hin,
            hi,if_true,if_false]
  have path := rowInterpolationPath ⟨b,ha⟩ (signedChordRows a S p n M) (signedChordBiases a S p n μ) hh
  have hj : JoinedIn (ExactSet N m k) b
      (withSecondRows b (signedChordRows a S p n M) (signedChordBiases a S p n μ)) :=
    ⟨path.map continuous_subtype_val,fun t=>(path t).property⟩
  exact hj

def baselineRow (U : Fin 2 → Fin 2 → ℝ) (s : ℝ) : Fin 6 → ℝ :=
  ![s,1-s,BaselineWeighted.anchorLeft U s,-BaselineWeighted.anchorLeft U s,
    BaselineWeighted.anchorRight U s,-BaselineWeighted.anchorRight U s]

theorem baselineRow_preact (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (x : Point 4) :
    preact (pairedRows U) 0 (baselineRow U s) 0 x=BaselineWeighted.weightedTarget s x := by
  have h := BaselineWeighted.anchor_identity U hU s x
  simp only [preact,Pi.zero_apply,add_zero,BaselineFold.first_activation]
  unfold BaselineFold.actualFeatures
  rw [BaselineFold.dot_features]
  change s*relu (x 0-x 1)+(1-s)*relu (x 2-x 3)+
    BaselineWeighted.anchorLeft U s*relu (BaselineFold.code U x 0)+
    (-BaselineWeighted.anchorLeft U s)*relu (-BaselineFold.code U x 0)+
    BaselineWeighted.anchorRight U s*relu (BaselineFold.code U x 1)+
    (-BaselineWeighted.anchorRight U s)*relu (-BaselineFold.code U x 1)=_
  dsimp [BaselineWeighted.weightedTarget]
  linear_combination h+BaselineWeighted.anchorLeft U s*(relu_sub_relu_neg (BaselineFold.code U x 0))+
    BaselineWeighted.anchorRight U s*(relu_sub_relu_neg (BaselineFold.code U x 1))

theorem baselineRow_eq_comparator (U : Fin 2 → Fin 2 → ℝ) (s : ℝ) :
    baselineRow U s=(fun j=>Paired.baselineRow U j+s*comparisonRow U j) := by
  funext j
  fin_cases j <;> simp [baselineRow,Paired.baselineRow,comparisonRow,
    BaselineWeighted.anchorLeft,BaselineWeighted.anchorRight,inverseCode] <;> ring

end MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
