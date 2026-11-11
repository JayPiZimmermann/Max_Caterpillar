import MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary.Aggregate

/-! # Physical ordinary-baseline paths to the quadrant endpoint -/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
open BigOperators Frontier BaselineFold Absorption
variable {m r : ℕ}

def carrierCoefficients (A : ℝ) (C : Fin m → Fin 6 → ℝ) : Fin m → ℝ := fun k => C k 0/A
def leftCoefficients (c : ℝ) (C : Fin m → Fin 6 → ℝ) : Fin m → ℝ :=
  fun k => negativeCoefficient c (C k 2) (C k 3)
def rightCoefficients (d : ℝ) (C : Fin m → Fin 6 → ℝ) : Fin m → ℝ :=
  fun k => negativeCoefficient d (C k 4) (C k 5)
def endpointCoefficients (c d : ℝ) (C : Fin m → Fin 6 → ℝ) : Fin m → ℝ :=
  fun k => retainedCoefficient c (leftCoefficients c C k) (rightCoefficients d C k)

def endpointRows (A B c d : ℝ) (C : Fin m → Fin 6 → ℝ) : Fin m → Fin 6 → ℝ :=
  fun k => liftTwoRow A B c d (carrierCoefficients A C k) (endpointCoefficients c d C k)

def endpointNet (U : Fin 2 → Fin 2 → ℝ) (swap : Bool) (A B c d : ℝ)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ) : Network 4 6 m :=
  orderedCompletion U swap (endpointRows A B c d C) bias weights θ

theorem domain_joinedIn_quadrant (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (hA : 0<A) (hB : 0≤B) (hcd : c≠0 ∨ d≠0)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : DomainFit C bias weights θ A B c d)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x, (appendSpectators (orderedCompletion U swap C bias weights θ)
      rows sbias sweights).eval x=Maximum 4 x) :
    JoinedIn (ExactSet 4 6 (m+r))
      (appendSpectators (orderedCompletion U swap C bias weights θ) rows sbias sweights)
      (appendSpectators (endpointNet U swap A B c d C bias weights θ) rows sbias sweights) ∧
    ∀ R N : ℝ, 0≤R → 0≤N →
      (∑ k, weights k*relu (carrierCoefficients A C k*R+
        endpointCoefficients c d C k*N+bias k))+θ=R-N := by
  let C₁ : ℝ → Fin m → Fin 6 → ℝ := fun t k => combineRow A B t (C k)
  let C₂ : ℝ → Fin m → Fin 6 → ℝ := fun t k => positiveFoldRow A c d t (C₁ 1 k)
  let a := carrierCoefficients A C
  let b := leftCoefficients c C
  let e := rightCoefficients d C
  let C₃ := aggregateRows A B c d a b e
  have h₁ : ∀ t : ℝ, 0≤t → t≤1 → DomainFit (C₁ t) bias weights θ A B c d := by
    intro t ht0 ht1
    exact combineRow_fit A B c d hA hB C bias weights θ hfit t ht0 ht1
  have h₂ : ∀ t : ℝ, 0≤t → t≤1 → DomainFit (C₂ t) bias weights θ A B c d := by
    intro t ht0 ht1
    exact positiveFoldRow_fit A B c d hA (C₁ 1) bias weights θ
      (h₁ 1 (by norm_num) le_rfl) t ht0 ht1
  have h₂one : C₂ 1=(fun k => liftThreeRow A B c d (a k) (b k) (e k)) := by
    funext k
    exact positive_fold_endpoint A B c d (ne_of_gt hA) (C k)
  have hthree : ThreeFit a b e bias weights θ c d := by
    apply threeFit_of_domainFit A B c d hA a b e bias weights θ
    rw [← h₂one]
    exact h₂ 1 (by norm_num) le_rfl
  have h₃ : ∀ t : ℝ, 0≤t → t≤1 → DomainFit (C₃ t) bias weights θ A B c d := by
    intro t ht0 ht1
    exact domainFit_of_threeFit A B c d hA.le hB a _ _ bias weights θ
      (aggregate_fit c d hcd a b e bias weights θ hthree t ht0 ht1)
  have h₁zero : C₁ 0=C := by
    funext k
    exact combineRow_zero A B (C k)
  have h₂zero : C₂ 0=C₁ 1 := by
    funext k
    exact positiveFoldRow_zero A c d (C₁ 1 k)
  have h₃zero : C₃ 0=C₂ 1 := by
    rw [h₂one]
    exact aggregateRows_zero A B c d a b e
  have h₃one : C₃ 1=endpointRows A B c d C := by
    exact aggregateRows_one A B c d a b e
  have hc₁ : Continuous C₁ := by
    apply continuous_pi
    intro k
    exact continuous_combineRow A B (C k)
  have hc₂ : Continuous C₂ := by
    apply continuous_pi
    intro k
    exact continuous_positiveFoldRow A c d (C₁ 1 k)
  have hs₁ : ∀ x, (appendSpectators (orderedCompletion U swap (C₁ 0) bias weights θ)
      rows sbias sweights).eval x=Maximum 4 x := by
    simpa only [h₁zero] using hsource
  have hs₂ : ∀ x, (appendSpectators (orderedCompletion U swap (C₂ 0) bias weights θ)
      rows sbias sweights).eval x=Maximum 4 x := by
    rw [h₂zero]
    exact append_exact_of_domainFit U swap C (C₁ 1) bias weights θ A B c d
      hfit (h₁ 1 (by norm_num) le_rfl) rows sbias sweights hsource
  have hs₃ : ∀ x, (appendSpectators (orderedCompletion U swap (C₃ 0) bias weights θ)
      rows sbias sweights).eval x=Maximum 4 x := by
    rw [h₃zero]
    exact append_exact_of_domainFit U swap C (C₂ 1) bias weights θ A B c d
      hfit (h₂ 1 (by norm_num) le_rfl) rows sbias sweights hsource
  have hj₁ := domain_path_joinedIn_exact U swap C₁ hc₁ bias weights θ A B c d h₁
    rows sbias sweights hs₁
  have hj₂ := domain_path_joinedIn_exact U swap C₂ hc₂ bias weights θ A B c d h₂
    rows sbias sweights hs₂
  have hj₃ := domain_path_joinedIn_exact U swap C₃
    (continuous_aggregateRows A B c d a b e) bias weights θ A B c d h₃
    rows sbias sweights hs₃
  rw [h₁zero] at hj₁
  rw [h₂zero] at hj₂
  rw [h₃zero,h₃one] at hj₃
  refine ⟨hj₁.trans (hj₂.trans hj₃),?_⟩
  have htwo : ThreeFit a (endpointCoefficients c d C) (endpointCoefficients c d C)
      bias weights θ c d := by
    simpa only [aggregateLeft_one,aggregateRight_one] using
      aggregate_fit c d hcd a b e bias weights θ hthree 1 (by norm_num) le_rfl
  exact quadrantFit_of_threeFit c d hcd a (endpointCoefficients c d C) bias weights θ htwo

/-- Arbitrary physical baseline completions, with an invertible code, reach
the explicit quadrant endpoint while arbitrary spectators remain fixed. -/
theorem physical_joinedIn_quadrant (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (swap : Bool) (A B c d : ℝ) (hA : 0<A) (hB : 0≤B) (hcd : c≠0 ∨ d≠0)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (orderedCompletion U swap C bias weights θ).eval x=orderedTarget U swap A B c d x)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x, (appendSpectators (orderedCompletion U swap C bias weights θ)
      rows sbias sweights).eval x=Maximum 4 x) :
    JoinedIn (ExactSet 4 6 (m+r))
      (appendSpectators (orderedCompletion U swap C bias weights θ) rows sbias sweights)
      (appendSpectators (endpointNet U swap A B c d C bias weights θ) rows sbias sweights) ∧
    ∀ R N : ℝ, 0≤R → 0≤N →
      (∑ k, weights k*relu (carrierCoefficients A C k*R+
        endpointCoefficients c d C k*N+bias k))+θ=R-N :=
  domain_joinedIn_quadrant U swap A B c d hA hB hcd C bias weights θ
    (domainFit_of_physical U hU swap C bias weights θ A B c d hfit)
    rows sbias sweights hsource

end MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
