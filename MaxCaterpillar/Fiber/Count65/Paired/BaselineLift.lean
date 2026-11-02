import MaxCaterpillar.Fiber.Count65.Paired.BaselineFold

/-! # Lifting quadrant coefficient paths to the fixed physical dictionary

The two endpoint coordinates of the mixed baseline fold are linear
combinations of the six fixed first features. This file provides the actual
coefficient map for lifting any subsequent quadrant coefficient deformation.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineLift
open BigOperators Frontier BaselineFold Absorption

variable {m r : ℕ}

def liftRow (A B c d a b : ℝ) : Fin 6 → ℝ :=
  ![a*A,b*B,a*relu c+b*relu (-c),a*relu (-c)+b*relu c,
    a*relu d+b*relu (-d),a*relu (-d)+b*relu d]

theorem liftRow_dot (U : Fin 2 → Fin 2 → ℝ) (A B c d a b : ℝ) (x : Point 4) :
    (∑ j, liftRow A B c d a b j*actualFeatures U x j)=
      a*positiveCoordinate U A c d x+b*negativeCoordinate U B c d x := by
  unfold actualFeatures
  rw [dot_features]
  change a*A*relu (x 0-x 1)+b*B*relu (x 2-x 3)+
    (a*relu c+b*relu (-c))*relu (code U x 0)+
    (a*relu (-c)+b*relu c)*relu (-code U x 0)+
    (a*relu d+b*relu (-d))*relu (code U x 1)+
    (a*relu (-d)+b*relu d)*relu (-code U x 1)=_
  dsimp [positiveCoordinate,negativeCoordinate,positiveAnchor,negativeAnchor]
  ring

/-- Endpoint equality holds as an equality of physical parameter rows. -/
theorem foldRow_one_eq_liftRow (A B c d : ℝ) (hA : A≠0) (hB : B≠0)
    (W : Fin 6 → ℝ) :
    foldRow A B c d 1 W=liftRow A B c d (W 0/A) (W 1/B) := by
  funext j
  fin_cases j <;> simp [foldRow,liftRow] <;> field_simp [hA,hB]

def quadrantNet (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (a b bias weights : Fin m → ℝ) (θ : ℝ) : Network 4 6 m :=
  completion U (fun k => liftRow A B c d (a k) (b k)) bias weights θ

theorem quadrantNet_eval (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (a b bias weights : Fin m → ℝ) (θ : ℝ) (x : Point 4) :
    (quadrantNet U A B c d a b bias weights θ).eval x=
      (∑ k, weights k*relu (a k*positiveCoordinate U A c d x+
        b k*negativeCoordinate U B c d x+bias k))+θ := by
  simp only [quadrantNet,completion_eval,liftRow_dot]

theorem foldedCompletion_one_eq_quadrantNet (U : Fin 2 → Fin 2 → ℝ)
    (A B c d : ℝ) (hA : A≠0) (hB : B≠0) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ) :
    foldedCompletion U A B c d C bias weights θ 1=
      quadrantNet U A B c d (fun k => C k 0/A) (fun k => C k 1/B) bias weights θ := by
  unfold foldedCompletion quadrantNet
  simp only [foldRow_one_eq_liftRow A B c d hA hB]

theorem continuous_quadrantNet {X : Type*} [TopologicalSpace X]
    (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (a b bias weights : X → Fin m → ℝ) (θ : X → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hδ : Continuous bias)
    (hw : Continuous weights) (hθ : Continuous θ) :
    Continuous (fun t => quadrantNet U A B c d (a t) (b t) (bias t) (weights t) (θ t)) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,hδ,hw,hθ⟩
  apply continuous_pi
  intro k
  apply continuous_pi
  intro j
  have hak := (continuous_apply k).comp ha
  have hbk := (continuous_apply k).comp hb
  fin_cases j <;> simp only [quadrantNet,completion,liftRow,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;> continuity

/-- An unrestricted quadrant identity is sufficient to certify the physical
lift. This is a proved model bridge, with no assumption about activation cells. -/
theorem quadrantNet_represents (U : Fin 2 → Fin 2 → ℝ) (A B c d ε : ℝ)
    (hA : 0≤A) (hB : 0≤B) (a b bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ Q N : ℝ, 0≤Q → 0≤N →
      (∑ k, weights k*relu (a k*Q+b k*N+bias k))+θ=ε*(Q-N))
    (x : Point 4) :
    (quadrantNet U A B c d a b bias weights θ).eval x=ε*target U A B c d x := by
  rw [quadrantNet_eval,target_coordinates]
  exact hfit _ _ (coordinates_nonneg U A B c d hA hB x).1
    (coordinates_nonneg U A B c d hA hB x).2

/-- Any continuous quadrant coefficient deformation lifts to an actual path
in the all-input exact fiber, while arbitrary spectator gates stay fixed. -/
theorem quadrant_path_joinedIn_exact (U : Fin 2 → Fin 2 → ℝ) (A B c d ε : ℝ)
    (hA : 0≤A) (hB : 0≤B)
    (a b bias weights : ℝ → Fin m → ℝ) (θ : ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hδ : Continuous bias)
    (hw : Continuous weights) (hθ : Continuous θ)
    (hfit : ∀ t : ℝ, 0≤t → t≤1 → ∀ Q N : ℝ, 0≤Q → 0≤N →
      (∑ k, weights t k*relu (a t k*Q+b t k*N+bias t k))+θ t=ε*(Q-N))
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x,
      (appendSpectators (quadrantNet U A B c d (a 0) (b 0) (bias 0) (weights 0) (θ 0))
        rows sbias sweights).eval x=Maximum 4 x) :
    JoinedIn (ExactSet 4 6 (m+r))
      (appendSpectators (quadrantNet U A B c d (a 0) (b 0) (bias 0) (weights 0) (θ 0)) rows sbias sweights)
      (appendSpectators (quadrantNet U A B c d (a 1) (b 1) (bias 1) (weights 1) (θ 1)) rows sbias sweights) := by
  have hc := continuous_appendSpectators
    (fun t => quadrantNet U A B c d (a t) (b t) (bias t) (weights t) (θ t))
    (continuous_quadrantNet U A B c d a b bias weights θ ha hb hδ hw hθ) rows sbias sweights
  apply JoinedIn.ofLine hc.continuousOn rfl rfl
  rintro _ ⟨t,ht,rfl⟩ x
  have hh := hsource x
  simp only [appendSpectators_eval] at hh ⊢
  rw [quadrantNet_represents U A B c d ε hA hB _ _ _ _ _
    (hfit 0 (by norm_num) (by norm_num))] at hh
  rw [quadrantNet_represents U A B c d ε hA hB _ _ _ _ _ (hfit t ht.1 ht.2)]
  exact hh

end MaxCaterpillar.Fiber.Count65.Paired.BaselineLift
