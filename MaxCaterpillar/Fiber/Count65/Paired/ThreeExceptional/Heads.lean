import MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional.Profile
import MaxCaterpillar.Fiber.Count65.Paired.SplitChord

/-! # Physical normalization of the two exceptional-profile baseline heads -/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
open BigOperators Frontier Absorption

lemma replace_profile_heads (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (R T : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ) (b₁ b₂ b₃ : Bool) :
    withSecondRows (profileNet U F G R weights b₁ b₂ b₃)
      (profileNet U F G T weights b₁ b₂ b₃).W₂
      (profileNet U F G T weights b₁ b₂ b₃).b₂=
        profileNet U F G T weights b₁ b₂ b₃ := rfl

theorem equal_head_preacts_joined (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (R T : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ) (b₁ b₂ b₃ : Bool)
    (heq : ∀ k x, preact (pairedRows U) 0 (T k) 0 x=preact (pairedRows U) 0 (R k) 0 x)
    (hnet : ∀ x, (profileNet U F G R weights b₁ b₂ b₃).eval x=Maximum 4 x) :
    JoinedIn (ExactSet 4 6 5) (profileNet U F G R weights b₁ b₂ b₃)
      (profileNet U F G T weights b₁ b₂ b₃) := by
  let a : ExactFiber 4 6 5 := ⟨profileNet U F G R weights b₁ b₂ b₃,hnet⟩
  have hrows : ∀ k, a.val.w₃ k≠0 → ∀ x,
      preact a.val.W₁ a.val.b₁ ((profileNet U F G T weights b₁ b₂ b₃).W₂ k)
        ((profileNet U F G T weights b₁ b₂ b₃).b₂ k) x=
      preact a.val.W₁ a.val.b₁ (a.val.W₂ k) (a.val.b₂ k) x := by
    intro k _ x
    refine Fin.addCases (motive := fun k : Fin (3+2) =>
      preact a.val.W₁ a.val.b₁ ((profileNet U F G T weights b₁ b₂ b₃).W₂ k)
        ((profileNet U F G T weights b₁ b₂ b₃).b₂ k) x=
      preact a.val.W₁ a.val.b₁ (a.val.W₂ k) (a.val.b₂ k) x)
      (fun i : Fin 3 => ?_) (fun i : Fin 2 => ?_) k
    · simp only [a,profileNet,switchingWithSpectators,appendSpectators,Fin.append_left]
    · simpa only [a,profileNet,switchingWithSpectators,appendSpectators,Fin.append_right] using heq i x
  have hp := rowInterpolationPath a (profileNet U F G T weights b₁ b₂ b₃).W₂
    (profileNet U F G T weights b₁ b₂ b₃).b₂ hrows
  have hh : JoinedIn (ExactSet 4 6 5) a.val
      (withSecondRows a.val (profileNet U F G T weights b₁ b₂ b₃).W₂
        (profileNet U F G T weights b₁ b₂ b₃).b₂) :=
    ⟨hp.map continuous_subtype_val,fun t => (hp t).property⟩
  simpa only [replace_profile_heads] using hh

def headSlots : Finset (Fin 5) := {3,4}

lemma profile_head_sum (U : Fin 2 → Fin 2 → ℝ) (F G P Q : Fin 6 → ℝ)
    (b₁ b₂ b₃ : Bool) (x : Point 4) :
    (∑ k in headSlots, (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃).w₃ k*
      relu (preact (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃).W₁
        (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃).b₁
        ((profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃).W₂ k)
        ((profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃).b₂ k) x))=
      relu (preact (pairedRows U) 0 P 0 x)-relu (preact (pairedRows U) 0 Q 0 x) := by
  rw [headSlots,Finset.sum_pair (by decide : (3:Fin 5)≠4)]
  change 1*relu (preact (pairedRows U) 0 P 0 x)+(-1)*relu (preact (pairedRows U) 0 Q 0 x)=_
  ring

lemma split_profile_rows (U : Fin 2 → Fin 2 → ℝ) (F G P Q H : Fin 6 → ℝ)
    (b₁ b₂ b₃ : Bool) :
    splitTargetRows (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃)
      (fun j => relu (H j)) (fun j => relu (-H j)) headSlots 3 4=
        (profileNet U F G (affineHeadRows true H) ![1,-1] b₁ b₂ b₃).W₂ := by
  funext k
  refine Fin.addCases (motive := fun k : Fin (3+2) =>
    splitTargetRows (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃)
      (fun j => relu (H j)) (fun j => relu (-H j)) headSlots 3 4 k=
        (profileNet U F G (affineHeadRows true H) ![1,-1] b₁ b₂ b₃).W₂ k)
    (fun i : Fin 3 => ?_) (fun i : Fin 2 => ?_) k
  · have h3 : (Fin.castAdd 2 i : Fin 5)≠3 := by fin_cases i <;> decide
    have h4 : (Fin.castAdd 2 i : Fin 5)≠4 := by fin_cases i <;> decide
    have hS : (Fin.castAdd 2 i : Fin 5)∉headSlots := by simp [headSlots,h3,h4]
    funext j
    simp only [splitTargetRows,if_neg h3,if_neg h4,if_neg hS]
    simp only [profileNet,switchingWithSpectators,appendSpectators,Fin.append_left]
  · fin_cases i
    · funext j
      simp only [splitTargetRows,if_pos rfl]
      change relu (H j)/(1:ℝ)=relu (H j)
      exact div_one _
    · funext j
      simp only [splitTargetRows,if_neg (by decide : (4:Fin 5)≠3),if_pos rfl]
      change -relu (-H j)/(-1:ℝ)=relu (-H j)
      ring

lemma split_profile_biases (U : Fin 2 → Fin 2 → ℝ) (F G P Q H : Fin 6 → ℝ)
    (b₁ b₂ b₃ : Bool) :
    splitTargetBiases (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃) 0 0 headSlots 3 4=
      (profileNet U F G (affineHeadRows true H) ![1,-1] b₁ b₂ b₃).b₂ := by
  funext k
  refine Fin.addCases (motive := fun k : Fin (3+2) =>
    splitTargetBiases (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃) 0 0 headSlots 3 4 k=
      (profileNet U F G (affineHeadRows true H) ![1,-1] b₁ b₂ b₃).b₂ k)
    (fun i : Fin 3 => ?_) (fun i : Fin 2 => ?_) k
  · have h3 : (Fin.castAdd 2 i : Fin 5)≠3 := by fin_cases i <;> decide
    have h4 : (Fin.castAdd 2 i : Fin 5)≠4 := by fin_cases i <;> decide
    have hS : (Fin.castAdd 2 i : Fin 5)∉headSlots := by simp [headSlots,h3,h4]
    simp only [splitTargetBiases,if_neg h3,if_neg h4,if_neg hS]
    simp only [profileNet,switchingWithSpectators,appendSpectators,Fin.append_left]
  · fin_cases i
    · simp only [splitTargetBiases,if_pos rfl,zero_div]
      rfl
    · simp only [splitTargetBiases,if_neg (by decide : (4:Fin 5)≠3),if_pos rfl,neg_zero,zero_div]
      rfl

theorem nonnegative_heads_joined_split (U : Fin 2 → Fin 2 → ℝ) (F G P Q H : Fin 6 → ℝ)
    (b₁ b₂ b₃ : Bool)
    (hP : ∀ x, 0≤preact (pairedRows U) 0 P 0 x)
    (hQ : ∀ x, 0≤preact (pairedRows U) 0 Q 0 x)
    (hfit : ∀ x, relu (preact (pairedRows U) 0 P 0 x)-relu (preact (pairedRows U) 0 Q 0 x)=
      preact (pairedRows U) 0 H 0 x)
    (hnet : ∀ x, (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃).eval x=Maximum 4 x) :
    JoinedIn (ExactSet 4 6 5) (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃)
      (profileNet U F G (affineHeadRows true H) ![1,-1] b₁ b₂ b₃) := by
  let net := profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃
  have hf : ∀ x, (∑ k in headSlots, net.w₃ k*relu (preact net.W₁ net.b₁ (net.W₂ k) (net.b₂ k) x))=
      preact net.W₁ net.b₁ (fun j => relu (H j)) 0 x-
        preact net.W₁ net.b₁ (fun j => relu (-H j)) 0 x := by
    intro x
    rw [profile_head_sum,hfit]
    have hh := preact_positive_parts_sub (pairedRows U) 0 H 0 x
    simpa only [show relu 0=0 from relu_of_nonneg le_rfl,neg_zero] using hh.symm
  have hj := splitChord_joinedIn_exact net (fun j => relu (H j)) (fun j => relu (-H j)) 0 0
    headSlots 3 4 (by simp [headSlots]) (by simp [headSlots]) (by decide)
    (by change (0:ℝ)<1; norm_num) (by change (-1:ℝ)<0; norm_num) hP hQ
    (fun x => by simpa only [show relu 0=0 from relu_of_nonneg le_rfl] using
      preact_positive_coefficients (pairedRows U) 0 H 0 x)
    (fun x => by simpa only [show relu 0=0 from relu_of_nonneg le_rfl,neg_zero] using
      preact_positive_coefficients (pairedRows U) 0 (fun j => -H j) 0 x) hf hnet
  rw [split_profile_rows,split_profile_biases,replace_profile_heads] at hj
  exact hj

lemma affineHeadBiases_zero (split : Bool) : affineHeadBiases split 0=(0:Fin 2 → ℝ) := by
  funext k
  cases split <;> fin_cases k <;> simp [affineHeadBiases,relu]

lemma compensated_start (U : Fin 2 → Fin 2 → ℝ) (F G H : Fin 6 → ℝ)
    (b₁ b₂ b₃ split : Bool) :
    switchingCompensatedNet (pairedRows U) 0 (comparisonRow U) F G H 0 0 0 0 0 b₁ b₂ b₃ split 0=
      profileNet U F G (affineHeadRows split H) ![1,-1] b₁ b₂ b₃ := by
  simp only [switchingCompensatedNet,profileNet,switchingWithSpectators,
    zero_mul,mul_zero,add_zero,affineHeadBiases_zero]

end MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
