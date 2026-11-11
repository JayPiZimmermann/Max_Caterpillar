import MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary.Paths

/-! # Genuine ordinary-baseline quadrant coordinates and physical path lifts -/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
open BigOperators Frontier BaselineFold Absorption
variable {m r : ℕ}

def positiveCoordinate (U : Fin 2 → Fin 2 → ℝ) (swap : Bool) (A B c d : ℝ) (x : Point 4) : ℝ :=
  totalPositive A B c d
    (if swap then relu (x 2-x 3) else relu (x 0-x 1))
    (if swap then relu (x 0-x 1) else relu (x 2-x 3)) (code U x 0) (code U x 1)

def negativeCoordinate (U : Fin 2 → Fin 2 → ℝ) (c d : ℝ) (x : Point 4) : ℝ :=
  negativePiece c (code U x 0)+negativePiece d (code U x 1)

lemma actualRow_dot (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d a b : ℝ) (x : Point 4) :
    (∑ j, liftTwoRow A B c d a b j*orderedFeatures U swap x j)=
      a*positiveCoordinate U swap A B c d x+b*negativeCoordinate U c d x := by
  simp only [orderedFeatures,actualFeatures,permRow_features,liftTwoRow_dot,
    positiveCoordinate,negativeCoordinate]

theorem coordinates_nonneg (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (hA : 0≤A) (hB : 0≤B) (x : Point 4) :
    0≤positiveCoordinate U swap A B c d x ∧ 0≤negativeCoordinate U c d x := by
  constructor
  · apply totalPositive_nonneg _ _ _ _ _ _ _ _ hA hB
    · cases swap <;> exact relu_nonneg _
    · cases swap <;> exact relu_nonneg _
  · exact add_nonneg (negativePiece_nonneg _ _) (negativePiece_nonneg _ _)

lemma domain_coordinates_surjective (A B c d : ℝ) (hA : 0<A) (hcd : c≠0 ∨ d≠0)
    (R N : ℝ) (hR : 0≤R) (hN : 0≤N) :
    ∃ q r u v : ℝ, 0≤q ∧ 0≤r ∧ totalPositive A B c d q r u v=R ∧
      negativePiece c u+negativePiece d v=N := by
  by_cases hc : c=0
  · have hd : d≠0 := hcd.resolve_left (by intro hn; exact hn hc)
    have hp := pieces_negative_realization d N hN (fun h => (hd h).elim)
    refine ⟨R/A,0,0,-N/d,div_nonneg hR hA.le,le_rfl,?_,?_⟩
    · unfold totalPositive
      rw [hp.1]
      simp only [mul_zero,add_zero,positivePiece_eq_relu,relu_of_nonneg le_rfl]
      field_simp [ne_of_gt hA]
      ring
    · rw [hp.2]
      simp [negativePiece_eq_relu,relu]
  · have hp := pieces_negative_realization c N hN (fun h => (hc h).elim)
    refine ⟨R/A,0,-N/c,0,div_nonneg hR hA.le,le_rfl,?_,?_⟩
    · unfold totalPositive
      rw [hp.1]
      simp only [mul_zero,add_zero,positivePiece_eq_relu,relu_of_nonneg le_rfl]
      field_simp [ne_of_gt hA]
      ring
    · rw [hp.2]
      simp [negativePiece_eq_relu,relu]

/-- The physical endpoint coordinates cover the whole closed quadrant. -/
theorem coordinates_surjective (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (swap : Bool) (A B c d : ℝ) (hA : 0<A) (hcd : c≠0 ∨ d≠0)
    (R N : ℝ) (hR : 0≤R) (hN : 0≤N) :
    ∃ x : Point 4, positiveCoordinate U swap A B c d x=R ∧ negativeCoordinate U c d x=N := by
  obtain ⟨q,r,u,v,hq,hr,hQ,hN'⟩ := domain_coordinates_surjective A B c d hA hcd R N hR hN
  obtain ⟨x,hx⟩ := orderedFeatures_surjective U hU swap q r u v hq hr
  refine ⟨x,?_,?_⟩
  · have hh := congrArg (fun F : Fin 6 → ℝ => ∑ j, liftTwoRow A B c d 1 0 j*F j) hx
    dsimp only at hh
    rw [actualRow_dot,liftTwoRow_dot,hQ] at hh
    simpa only [one_mul,zero_mul,add_zero] using hh
  · have hh := congrArg (fun F : Fin 6 → ℝ => ∑ j, liftTwoRow A B c d 0 1 j*F j) hx
    dsimp only at hh
    rw [actualRow_dot,liftTwoRow_dot,hN'] at hh
    simpa only [one_mul,zero_mul,zero_add] using hh

lemma target_coordinates (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (x : Point 4) :
    orderedTarget U swap A B c d x=
      positiveCoordinate U swap A B c d x-negativeCoordinate U c d x := by
  simp only [orderedTarget,orderedFeatures,actualFeatures,permRow_features,positiveRow_dot,
    positiveCoordinate,negativeCoordinate]
  rw [target_three_coordinates]
  ring

def quadrantNet (U : Fin 2 → Fin 2 → ℝ) (swap : Bool) (A B c d : ℝ)
    (a b bias weights : Fin m → ℝ) (θ : ℝ) : Network 4 6 m :=
  orderedCompletion U swap (fun k => liftTwoRow A B c d (a k) (b k)) bias weights θ

theorem endpointNet_eq_quadrantNet (U : Fin 2 → Fin 2 → ℝ) (swap : Bool) (A B c d : ℝ)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ) :
    endpointNet U swap A B c d C bias weights θ=
      quadrantNet U swap A B c d (carrierCoefficients A C) (endpointCoefficients c d C) bias weights θ := rfl

lemma quadrantNet_eval (U : Fin 2 → Fin 2 → ℝ) (swap : Bool) (A B c d : ℝ)
    (a b bias weights : Fin m → ℝ) (θ : ℝ) (x : Point 4) :
    (quadrantNet U swap A B c d a b bias weights θ).eval x=
      (∑ k, weights k*relu (a k*positiveCoordinate U swap A B c d x+
        b k*negativeCoordinate U c d x+bias k))+θ := by
  simp only [quadrantNet,orderedCompletion_eval,actualRow_dot]

theorem continuous_quadrantNet {X : Type*} [TopologicalSpace X]
    (U : Fin 2 → Fin 2 → ℝ) (swap : Bool) (A B c d : ℝ)
    (a b bias weights : X → Fin m → ℝ) (θ : X → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hδ : Continuous bias)
    (hw : Continuous weights) (hθ : Continuous θ) :
    Continuous (fun t => quadrantNet U swap A B c d (a t) (b t) (bias t) (weights t) (θ t)) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,hδ,hw,hθ⟩
  apply continuous_pi
  intro k
  apply continuous_permRow swap
  apply continuous_pi
  intro j
  have hak := (continuous_apply k).comp ha
  have hbk := (continuous_apply k).comp hb
  fin_cases j <;> simp only [quadrantNet,orderedCompletion,completion,liftTwoRow,liftThreeRow,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;> continuity

theorem quadrantNet_represents (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (hA : 0≤A) (hB : 0≤B)
    (a b bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ R N : ℝ, 0≤R → 0≤N →
      (∑ k, weights k*relu (a k*R+b k*N+bias k))+θ=R-N) (x : Point 4) :
    (quadrantNet U swap A B c d a b bias weights θ).eval x=orderedTarget U swap A B c d x := by
  rw [quadrantNet_eval,target_coordinates]
  exact hfit _ _ (coordinates_nonneg U swap A B c d hA hB x).1
    (coordinates_nonneg U swap A B c d hA hB x).2

/-- An arbitrary continuous quadrant coefficient path lifts to actual fixed-
dictionary network parameters, including arbitrary unchanged spectators. -/
theorem quadrant_path_joinedIn_exact (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (A B c d : ℝ) (hA : 0≤A) (hB : 0≤B)
    (a b bias weights : ℝ → Fin m → ℝ) (θ : ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hδ : Continuous bias)
    (hw : Continuous weights) (hθ : Continuous θ)
    (hfit : ∀ t : ℝ, 0≤t → t≤1 → ∀ R N : ℝ, 0≤R → 0≤N →
      (∑ k, weights t k*relu (a t k*R+b t k*N+bias t k))+θ t=R-N)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x, (appendSpectators
      (quadrantNet U swap A B c d (a 0) (b 0) (bias 0) (weights 0) (θ 0))
      rows sbias sweights).eval x=Maximum 4 x) :
    JoinedIn (ExactSet 4 6 (m+r))
      (appendSpectators (quadrantNet U swap A B c d (a 0) (b 0) (bias 0) (weights 0) (θ 0)) rows sbias sweights)
      (appendSpectators (quadrantNet U swap A B c d (a 1) (b 1) (bias 1) (weights 1) (θ 1)) rows sbias sweights) := by
  have hc := continuous_appendSpectators
    (fun t => quadrantNet U swap A B c d (a t) (b t) (bias t) (weights t) (θ t))
    (continuous_quadrantNet U swap A B c d a b bias weights θ ha hb hδ hw hθ) rows sbias sweights
  apply JoinedIn.ofLine hc.continuousOn rfl rfl
  rintro _ ⟨t,ht,rfl⟩ x
  have hh := hsource x
  simp only [appendSpectators_eval] at hh ⊢
  rw [quadrantNet_represents U swap A B c d hA hB _ _ _ _ _ (hfit 0 (by norm_num) (by norm_num))] at hh
  rw [quadrantNet_represents U swap A B c d hA hB _ _ _ _ _ (hfit t ht.1 ht.2)]
  exact hh

end MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
