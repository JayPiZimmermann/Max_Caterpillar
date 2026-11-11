import MaxCaterpillar.Fiber.Count65.Paired.BaselineEndpoint

/-! # All-real weighted baseline fold data for physical quadrant attachment -/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineEndpointFold
open BigOperators Frontier Absorption BaselineEndpoint
variable {m r : ℕ}

/-- An actual zero-bias local endpoint, with its two nonnegative physical
carrier rows and its unrestricted quadrant coefficient identity. -/
structure EndpointData (U : Fin 2 → Fin 2 → ℝ) (weights : Fin m → ℝ) (s : ℝ) where
  block : Network 4 6 m
  positiveRow : Fin 6 → ℝ
  negativeRow : Fin 6 → ℝ
  a : Fin m → ℝ
  b : Fin m → ℝ
  firstMatrix : block.W₁=pairedRows U
  firstBias : block.b₁=0
  secondBias : block.b₂=0
  readout : block.w₃=weights
  outputBias : block.b₃=0
  rows : ∀ k, block.W₂ k=(fun j => a k*positiveRow j+b k*negativeRow j)
  quadrantFit : ∀ Q N : ℝ, 0≤Q → 0≤N →
    (∑ k, weights k*relu (a k*Q+b k*N))=Q-N
  positive : ∀ x, 0≤preact (pairedRows U) 0 positiveRow 0 x
  negative : ∀ x, 0≤preact (pairedRows U) 0 negativeRow 0 x
  difference : ∀ x, preact (pairedRows U) 0 (fun j => positiveRow j-negativeRow j) 0 x=
    BaselineWeighted.weightedTarget s x

lemma mixed_quadrant_fit (A B ε : ℝ) (C : Fin m → Fin 6 → ℝ) (weights : Fin m → ℝ)
    (hε : ε=1 ∨ ε=-1)
    (hfit : ∀ Q N : ℝ, 0≤Q → 0≤N →
      (∑ k, weights k*relu (C k 0/A*Q+C k 1/B*N))=ε*(Q-N)) :
    ∀ Q N : ℝ, 0≤Q → 0≤N →
      (∑ k, weights k*relu (mixedFirstCoefficient A B ε (C k)*Q+
        mixedSecondCoefficient A B ε (C k)*N))=Q-N := by
  intro Q N hQ hN
  rcases hε with rfl|rfl
  · simpa only [mixedFirstCoefficient,mixedSecondCoefficient,if_true,one_mul] using hfit Q N hQ hN
  · have hh := hfit N Q hN hQ
    have harg : ∀ k, C k 0/A*N+C k 1/B*Q=C k 1/B*Q+C k 0/A*N := by
      intro k
      ring
    simp_rw [harg] at hh
    simpa only [mixedFirstCoefficient,mixedSecondCoefficient,show (-1:ℝ)≠1 by norm_num,
      if_false,neg_one_mul,neg_sub] using hh

/-- Every actual zero-bias weighted baseline, for every real weight `s`,
connects to packaged physical quadrant data. All arbitrary spectator gates
are fixed throughout the coefficient paths. No quadrant classification or
connectivity premise is assumed. -/
theorem weighted_baseline_fold_data (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (C : Fin m → Fin 6 → ℝ) (weights : Fin m → ℝ)
    (hfit : ∀ x, (BaselineFold.completion U C 0 weights 0).eval x=BaselineWeighted.weightedTarget s x)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x, (appendSpectators (BaselineFold.completion U C 0 weights 0)
      rows sbias sweights).eval x=Maximum 4 x) :
    ∃ data : EndpointData U weights s,
      JoinedIn (ExactSet 4 6 (m+r))
        (appendSpectators (BaselineFold.completion U C 0 weights 0) rows sbias sweights)
        (appendSpectators data.block rows sbias sweights) := by
  by_cases hs : s<0 ∨ 1<s
  · obtain ⟨A,B,c,d,ε,hA,hB,hε,htarget,hjoined⟩ :=
      BaselineWeighted.mixed_weighted_joinedIn_exact U hU s hs C 0 weights 0 hfit rows sbias sweights hsource
    have hfit' : ∀ x, (BaselineFold.completion U C 0 weights 0).eval x=
        ε*BaselineFold.target U A B c d x := by
      intro x
      exact (hfit x).trans (htarget x)
    have hquad : ∀ Q N : ℝ, 0≤Q → 0≤N →
        (∑ k, weights k*relu (C k 0/A*Q+C k 1/B*N))=ε*(Q-N) := by
      intro Q N hQ hN
      simpa only [Pi.zero_apply,add_zero] using
        BaselineFold.physical_quadrant_identity_smul U A B c d ε hA hB C 0 weights 0 hfit' Q N hQ hN
    let data : EndpointData U weights s := {
      block := BaselineFold.foldedCompletion U A B c d C 0 weights 0 1
      positiveRow := mixedQRow A B c d ε
      negativeRow := mixedRRow A B c d ε
      a := fun k => mixedFirstCoefficient A B ε (C k)
      b := fun k => mixedSecondCoefficient A B ε (C k)
      firstMatrix := rfl
      firstBias := rfl
      secondBias := rfl
      readout := rfl
      outputBias := rfl
      rows := mixed_physical_endpoint_row_factor U A B c d ε (ne_of_gt hA) (ne_of_gt hB) C 0 weights 0
      quadrantFit := mixed_quadrant_fit A B ε C weights hε hquad
      positive := fun x => (mixed_carriers_nonneg U A B c d ε hA.le hB.le x).1
      negative := fun x => (mixed_carriers_nonneg U A B c d ε hA.le hB.le x).2
      difference := mixed_weighted_carriers_subtract U A B c d ε s hε htarget
    }
    exact ⟨data,hjoined⟩
  · have hs0 : 0≤s := le_of_not_gt (fun h => hs (Or.inl h))
    have hs1 : s≤1 := le_of_not_gt (fun h => hs (Or.inr h))
    obtain ⟨swap,A,B,hA,hB,htarget,hjoined,hquad⟩ :=
      BaselineOrdinary.ordinary_weighted_joinedIn_quadrant U hU s hs0 hs1 C 0 weights 0 hfit
        rows sbias sweights hsource
    let c := BaselineWeighted.anchorLeft U s
    let d := BaselineWeighted.anchorRight U s
    let D : Fin m → Fin 6 → ℝ := fun k => BaselineOrdinary.permRow swap (C k)
    let data : EndpointData U weights s := {
      block := BaselineOrdinary.endpointNet U swap A B c d D 0 weights 0
      positiveRow := ordinaryQRow swap A B c d
      negativeRow := ordinaryRRow swap A B c d
      a := BaselineOrdinary.carrierCoefficients A D
      b := BaselineOrdinary.endpointCoefficients c d D
      firstMatrix := rfl
      firstBias := rfl
      secondBias := rfl
      readout := rfl
      outputBias := rfl
      rows := ordinary_endpoint_row_factor U swap A B c d D 0 weights 0
      quadrantFit := fun Q N hQ hN => by simpa only [Pi.zero_apply,add_zero] using hquad Q N hQ hN
      positive := fun x => (ordinary_carriers_nonneg U swap A B c d hA.le hB x).1
      negative := fun x => (ordinary_carriers_nonneg U swap A B c d hA.le hB x).2
      difference := ordinary_weighted_carriers_subtract U swap A B c d s htarget
    }
    exact ⟨data,hjoined⟩

end MaxCaterpillar.Fiber.Count65.Paired.BaselineEndpointFold
