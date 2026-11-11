import MaxCaterpillar.Fiber.Count65.Paired.BaselineWeighted

/-! # Actual-network bridge for ordinary weighted-baseline coefficient paths

An invertible anchor code realizes the full product of two nonnegative
increments and two real code coordinates. The optional outgoing-column swap
only chooses which increment carries the positive folding; the actual first
layer and all physical first-neuron labels remain fixed.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
open BigOperators Frontier BaselineFold Absorption
variable {m r : ℕ}

def permRow (swap : Bool) (W : Fin 6 → ℝ) : Fin 6 → ℝ :=
  if swap then ![W 1,W 0,W 2,W 3,W 4,W 5] else W

lemma permRow_involutive (swap : Bool) (W : Fin 6 → ℝ) :
    permRow swap (permRow swap W)=W := by
  cases swap
  · rfl
  · funext j
    fin_cases j <;> simp [permRow] <;> rfl

private lemma sum_six (f : Fin 6 → ℝ) :
    (∑ j, f j)=f 0+(f 1+(f 2+(f 3+(f 4+f 5)))) := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rfl

lemma dot_permRow (swap : Bool) (W F : Fin 6 → ℝ) :
    (∑ j, permRow swap W j*F j)=∑ j, W j*permRow swap F j := by
  cases swap
  · rfl
  · rw [sum_six,sum_six]
    change W 1*F 0+(W 0*F 1+(W 2*F 2+(W 3*F 3+(W 4*F 4+W 5*F 5))))=
      W 0*F 1+(W 1*F 0+(W 2*F 2+(W 3*F 3+(W 4*F 4+W 5*F 5))))
    ring

lemma permRow_features (swap : Bool) (q r u v : ℝ) :
    permRow swap (features q r u v)=
      features (if swap then r else q) (if swap then q else r) u v := by
  cases swap
  · rfl
  · rfl

lemma actualFeatures_probe (U : Fin 2 → Fin 2 → ℝ) (a b q r : ℝ)
    (hq : 0≤q) (hr : 0≤r) :
    actualFeatures U ![a+q,a,b+r,b]=
      features q r (U 0 0*a+U 0 1*b) (U 1 0*a+U 1 1*b) := by
  change features (relu (a+q-a)) (relu (b+r-b))
    (U 0 0*a+U 0 1*b) (U 1 0*a+U 1 1*b)=_
  rw [show a+q-a=q by ring,show b+r-b=r by ring,
    relu_of_nonneg hq,relu_of_nonneg hr]

theorem actualFeatures_surjective (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (q r u v : ℝ) (hq : 0≤q) (hr : 0≤r) :
    ∃ x : Point 4, actualFeatures U x=features q r u v := by
  let R := inverseCode U
  have hcode := code_rightInverse_eval U R (inverseCode_rightInverse U hU) u v
  refine ⟨![(R 0 0*u+R 0 1*v)+q,R 0 0*u+R 0 1*v,
    (R 1 0*u+R 1 1*v)+r,R 1 0*u+R 1 1*v],?_⟩
  rw [actualFeatures_probe U _ _ q r hq hr,hcode.1,hcode.2]

def orderedFeatures (U : Fin 2 → Fin 2 → ℝ) (swap : Bool) (x : Point 4) : Fin 6 → ℝ :=
  permRow swap (actualFeatures U x)

theorem orderedFeatures_surjective (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (swap : Bool) (q r u v : ℝ) (hq : 0≤q) (hr : 0≤r) :
    ∃ x : Point 4, orderedFeatures U swap x=features q r u v := by
  cases swap
  · exact actualFeatures_surjective U hU q r u v hq hr
  · obtain ⟨x,hx⟩ := actualFeatures_surjective U hU r q u v hr hq
    refine ⟨x,?_⟩
    unfold orderedFeatures
    rw [hx,permRow_features]
    rfl

def positiveRow (A B c d : ℝ) : Fin 6 → ℝ := ![A,B,c,-c,d,-d]

lemma positiveRow_dot (A B c d q r u v : ℝ) :
    (∑ j, positiveRow A B c d j*features q r u v j)=A*q+B*r+c*u+d*v := by
  rw [dot_features]
  change A*q+B*r+c*relu u+(-c)*relu (-u)+d*relu v+(-d)*relu (-v)=_
  linear_combination c*(relu_sub_relu_neg u)+d*(relu_sub_relu_neg v)

def orderedTarget (U : Fin 2 → Fin 2 → ℝ) (swap : Bool) (A B c d : ℝ)
    (x : Point 4) : ℝ := ∑ j, positiveRow A B c d j*orderedFeatures U swap x j

def DomainFit (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ A B c d : ℝ) : Prop :=
  ∀ q r u v : ℝ, 0≤q → 0≤r →
    (∑ k, weights k*relu ((∑ j, C k j*features q r u v j)+bias k))+θ=A*q+B*r+c*u+d*v

def orderedCompletion (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ) : Network 4 6 m :=
  completion U (fun k => permRow swap (C k)) bias weights θ

lemma orderedCompletion_eval (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ) (x : Point 4) :
    (orderedCompletion U swap C bias weights θ).eval x=
      (∑ k, weights k*relu ((∑ j, C k j*orderedFeatures U swap x j)+bias k))+θ := by
  simp only [orderedCompletion,completion_eval,dot_permRow,orderedFeatures]

theorem domainFit_of_physical (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (swap : Bool) (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ A B c d : ℝ)
    (hfit : ∀ x, (orderedCompletion U swap C bias weights θ).eval x=orderedTarget U swap A B c d x) :
    DomainFit C bias weights θ A B c d := by
  intro q r u v hq hr
  obtain ⟨x,hx⟩ := orderedFeatures_surjective U hU swap q r u v hq hr
  have hh := hfit x
  rw [orderedCompletion_eval,orderedTarget,hx,positiveRow_dot] at hh
  exact hh

theorem physical_of_domainFit (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ A B c d : ℝ)
    (hfit : DomainFit C bias weights θ A B c d) (x : Point 4) :
    (orderedCompletion U swap C bias weights θ).eval x=orderedTarget U swap A B c d x := by
  rw [orderedCompletion_eval,orderedTarget]
  simp only [orderedFeatures,actualFeatures,permRow_features,positiveRow_dot]
  apply hfit
  · cases swap <;> exact relu_nonneg _
  · cases swap <;> exact relu_nonneg _

theorem append_exact_of_domainFit (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (C D : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ A B c d : ℝ)
    (hC : DomainFit C bias weights θ A B c d) (hD : DomainFit D bias weights θ A B c d)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x, (appendSpectators (orderedCompletion U swap C bias weights θ)
      rows sbias sweights).eval x=Maximum 4 x) (x : Point 4) :
    (appendSpectators (orderedCompletion U swap D bias weights θ) rows sbias sweights).eval x=Maximum 4 x := by
  have hh := hsource x
  simp only [appendSpectators_eval] at hh ⊢
  rw [physical_of_domainFit U swap C bias weights θ A B c d hC] at hh
  rw [physical_of_domainFit U swap D bias weights θ A B c d hD]
  exact hh

lemma continuous_permRow {X : Type*} [TopologicalSpace X] (swap : Bool)
    (W : X → Fin 6 → ℝ) (hW : Continuous W) :
    Continuous (fun t => permRow swap (W t)) := by
  cases swap
  · exact hW
  · apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun t => W t 1)
      exact (continuous_apply 1).comp hW
    · change Continuous (fun t => W t 0)
      exact (continuous_apply 0).comp hW
    · change Continuous (fun t => W t 2)
      exact (continuous_apply 2).comp hW
    · change Continuous (fun t => W t 3)
      exact (continuous_apply 3).comp hW
    · change Continuous (fun t => W t 4)
      exact (continuous_apply 4).comp hW
    · change Continuous (fun t => W t 5)
      exact (continuous_apply 5).comp hW

theorem continuous_orderedCompletion (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (C : ℝ → Fin m → Fin 6 → ℝ) (hC : Continuous C)
    (bias weights : Fin m → ℝ) (θ : ℝ) :
    Continuous (fun t => orderedCompletion U swap (C t) bias weights θ) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,continuous_const,continuous_const,continuous_const⟩
  apply continuous_pi
  intro k
  exact continuous_permRow swap (fun t => C t k) ((continuous_apply k).comp hC)

/-- Every domain-fit coefficient homotopy is a physical exact-fiber path with
all spectator rows, biases, and outputs unchanged. -/
theorem domain_path_joinedIn_exact (U : Fin 2 → Fin 2 → ℝ) (swap : Bool)
    (C : ℝ → Fin m → Fin 6 → ℝ) (hC : Continuous C)
    (bias weights : Fin m → ℝ) (θ A B c d : ℝ)
    (hfit : ∀ t : ℝ, 0≤t → t≤1 → DomainFit (C t) bias weights θ A B c d)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x, (appendSpectators (orderedCompletion U swap (C 0) bias weights θ)
      rows sbias sweights).eval x=Maximum 4 x) :
    JoinedIn (ExactSet 4 6 (m+r))
      (appendSpectators (orderedCompletion U swap (C 0) bias weights θ) rows sbias sweights)
      (appendSpectators (orderedCompletion U swap (C 1) bias weights θ) rows sbias sweights) := by
  have hc := continuous_appendSpectators
    (fun t => orderedCompletion U swap (C t) bias weights θ)
    (continuous_orderedCompletion U swap C hC bias weights θ) rows sbias sweights
  apply JoinedIn.ofLine hc.continuousOn rfl rfl
  rintro _ ⟨t,ht,rfl⟩ x
  have hh := hsource x
  simp only [appendSpectators_eval] at hh ⊢
  rw [physical_of_domainFit U swap _ _ _ _ A B c d (hfit 0 (by norm_num) (by norm_num))] at hh
  rw [physical_of_domainFit U swap _ _ _ _ A B c d (hfit t ht.1 ht.2)]
  exact hh

end MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
