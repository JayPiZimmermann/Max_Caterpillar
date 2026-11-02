import MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary.Coordinates

/-! # Ordinary weighted baselines over arbitrary invertible paired codes

Every physical completion representing the weighted baseline with `0≤s≤1`
has an actual coefficient path to the full-quadrant endpoint. The physical
first dictionary and arbitrary spectator second neurons stay fixed. This is
the missing ordinary counterpart of `BaselineWeighted`'s mixed reduction;
connectivity of arbitrary quadrant completions is a separate obligation.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
open BigOperators Frontier BaselineFold BaselineWeighted Absorption
variable {m r : ℕ}

lemma orderedCompletion_perm (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ) :
    orderedCompletion U swap (fun k => permRow swap (C k)) bias weights θ=
      completion U C bias weights θ := by
  simp only [orderedCompletion,permRow_involutive]

lemma weighted_anchor_nonzero (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) (s : ℝ) :
    anchorLeft U s≠0 ∨ anchorRight U s≠0 := by
  by_contra h
  have hc : anchorLeft U s=0 := not_ne_iff.mp (not_or.mp h).1
  have hd : anchorRight U s=0 := not_ne_iff.mp (not_or.mp h).2
  have ha := anchor_identity U hU s (![0,1,0,0] : Point 4)
  have hb := anchor_identity U hU s (![0,0,0,1] : Point 4)
  rw [hc,hd,zero_mul,zero_mul,zero_add] at ha hb
  change 0=s*1+(1-s)*0 at ha
  change 0=s*0+(1-s)*1 at hb
  linarith only [ha,hb]

lemma weighted_ordered_target (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (swap : Bool) (s : ℝ) (x : Point 4) :
    orderedTarget U swap (if swap then 1-s else s) (if swap then s else 1-s)
      (anchorLeft U s) (anchorRight U s) x=weightedTarget s x := by
  simp only [orderedTarget,orderedFeatures,actualFeatures,permRow_features,positiveRow_dot]
  cases swap
  · change s*relu (x 0-x 1)+(1-s)*relu (x 2-x 3)+
      anchorLeft U s*code U x 0+anchorRight U s*code U x 1=weightedTarget s x
    unfold weightedTarget
    linear_combination anchor_identity U hU s x
  · change (1-s)*relu (x 2-x 3)+s*relu (x 0-x 1)+
      anchorLeft U s*code U x 0+anchorRight U s*code U x 1=weightedTarget s x
    unfold weightedTarget
    linear_combination anchor_identity U hU s x

theorem ordinary_weighted_normal_form (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (hs0 : 0≤s) (hs1 : s≤1) :
    ∃ swap : Bool, ∃ A B : ℝ, 0<A ∧ 0≤B ∧
      ∀ x, orderedTarget U swap A B (anchorLeft U s) (anchorRight U s) x=weightedTarget s x := by
  by_cases hs : s=0
  · refine ⟨true,1,0,by norm_num,le_rfl,?_⟩
    intro x
    simpa only [hs,sub_zero] using weighted_ordered_target U hU true s x
  · refine ⟨false,s,1-s,lt_of_le_of_ne hs0 (Ne.symm hs),sub_nonneg.mpr hs1,?_⟩
    exact weighted_ordered_target U hU false s

/-- Every ordinary weighted baseline completion reaches the explicit physical
quadrant endpoint. The source rows and outputs are arbitrary real parameters;
the zero anchor-coefficient and endpoint-weight cases are included. -/
theorem ordinary_weighted_joinedIn_quadrant (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (hs0 : 0≤s) (hs1 : s≤1)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=weightedTarget s x)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x, (appendSpectators (completion U C bias weights θ)
      rows sbias sweights).eval x=Maximum 4 x) :
    ∃ swap : Bool, ∃ A B : ℝ, 0<A ∧ 0≤B ∧
      (∀ x, orderedTarget U swap A B (anchorLeft U s) (anchorRight U s) x=weightedTarget s x) ∧
      JoinedIn (ExactSet 4 6 (m+r))
        (appendSpectators (completion U C bias weights θ) rows sbias sweights)
        (appendSpectators (endpointNet U swap A B (anchorLeft U s) (anchorRight U s)
          (fun k => permRow swap (C k)) bias weights θ) rows sbias sweights) ∧
      ∀ R N : ℝ, 0≤R → 0≤N →
        (∑ k, weights k*relu (carrierCoefficients A (fun i => permRow swap (C i)) k*R+
          endpointCoefficients (anchorLeft U s) (anchorRight U s)
            (fun i => permRow swap (C i)) k*N+bias k))+θ=R-N := by
  obtain ⟨swap,A,B,hA,hB,htarget⟩ := ordinary_weighted_normal_form U hU s hs0 hs1
  let D : Fin m → Fin 6 → ℝ := fun k => permRow swap (C k)
  have hfit' : ∀ x, (orderedCompletion U swap D bias weights θ).eval x=
      orderedTarget U swap A B (anchorLeft U s) (anchorRight U s) x := by
    intro x
    rw [orderedCompletion_perm,hfit]
    exact (htarget x).symm
  have hsource' : ∀ x, (appendSpectators (orderedCompletion U swap D bias weights θ)
      rows sbias sweights).eval x=Maximum 4 x := by
    simpa only [orderedCompletion_perm] using hsource
  obtain ⟨hj,hq⟩ := physical_joinedIn_quadrant U hU swap A B (anchorLeft U s) (anchorRight U s)
    hA hB (weighted_anchor_nonzero U hU s) D bias weights θ hfit' rows sbias sweights hsource'
  refine ⟨swap,A,B,hA,hB,htarget,?_,hq⟩
  simpa only [orderedCompletion_perm] using hj

end MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
