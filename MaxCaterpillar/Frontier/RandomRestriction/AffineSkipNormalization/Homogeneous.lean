import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Localization

/-! # An exact directional model for arbitrary affine skips

One extra input coordinate encodes constants, not a neuron. Localizing at
that coordinate's unit vector removes the biases while retaining both
original neuron index types. All equalities hold for arbitrary real arrays.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
open BigOperators
open NormalizedNetwork
variable {N h₁ h₂ : ℕ}

def originalCoordinates (N : ℕ) : Fin N ↪ Fin (N+1) :=
  ⟨Fin.succ,Fin.succ_injective N⟩

def constantPoint (N : ℕ) : Point (N+1) := Fin.cons 1 0

def affinePoint (x : Point N) : Point (N+1) := Fin.cons 1 x

lemma lin_cons (a : Point N) (b : ℝ) (x : Point N) :
    lin (Fin.cons b a) (affinePoint x) = lin a x+b := by
  simp only [lin,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,affinePoint]
  simp only [Fin.cons_zero,Fin.cons_succ,mul_one]
  ring

lemma lin_constantPoint (a : Point N) (b : ℝ) :
    lin (Fin.cons b a) (constantPoint N) = b := by
  simp [lin,constantPoint,Fin.sum_univ_succ]

lemma restrict_cons (a : Point N) (b : ℝ) :
    restrict (originalCoordinates N) (Fin.cons b a) = a := by
  rfl

lemma lifted_direction_zero (x : Point N) :
    lift (originalCoordinates N) x 0 = 0 := by
  apply lift_outside
  simp [originalCoordinates]

lemma affinePoint_step (ε : ℝ) (x : Point N) :
    constantPoint N+ε • lift (originalCoordinates N) x = affinePoint (ε • x) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [constantPoint,affinePoint,lifted_direction_zero]
  · change (0:Point N) i+ε*lift (originalCoordinates N) x ((originalCoordinates N) i)=ε*x i
    rw [lift_selected]
    simp

/-- The extra input is exactly the constant coordinate; there are no new
first-hidden-layer or second-hidden-layer slots. -/
noncomputable def homogeneousExtension (net : AffineSkipNetwork N h₁ h₂) :
    NormalizedNetwork (N+1) h₁ h₂ where
  A j := Fin.cons (net.b j) (net.A j)
  U k := Fin.cons (net.θ k) (net.U k)
  W := net.W
  L := Fin.cons net.β net.L
  B := net.B
  d := net.d

lemma homogeneousExtension_inner (net : AffineSkipNetwork N h₁ h₂)
    (k : Fin h₂) (x : Point N) :
    (homogeneousExtension net).inner k (affinePoint x) = inner net k x := by
  simp only [NormalizedNetwork.inner,homogeneousExtension,lin_cons]
  unfold inner first
  change (lin (net.U k) x+net.θ k)+(∑ j,net.W k j*relu (lin (net.A j) x+net.b j))=_
  simp only [lin]
  ring

/-- Evaluation agrees with the original nine-array affine-skip evaluator. -/
theorem homogeneousExtension_eval (net : AffineSkipNetwork N h₁ h₂) (x : Point N) :
    (homogeneousExtension net).eval (affinePoint x) = eval net x := by
  simp only [NormalizedNetwork.eval,homogeneousExtension_inner]
  change lin (Fin.cons net.β net.L) (affinePoint x)+
    (∑ j,net.B j*relu (lin (Fin.cons (net.b j) (net.A j)) (affinePoint x)))+
    (∑ k,net.d k*relu (inner net k x))=_
  simp only [lin_cons]
  unfold eval outputSkip first
  simp only [lin]
  ring

/-- The exact first-order network at the original input origin. -/
noncomputable def homogeneousModel (net : AffineSkipNetwork N h₁ h₂) :
    NormalizedNetwork N h₁ h₂ :=
  (homogeneousExtension net).localize (constantPoint N) (originalCoordinates N)

theorem homogeneousModel_first_row (net : AffineSkipNetwork N h₁ h₂) (j : Fin h₁) :
    (homogeneousModel net).A j = if net.b j=0 then net.A j else 0 := by
  rw [homogeneousModel,localize_first_row]
  simp only [homogeneousExtension,lin_constantPoint,restrict_cons]

theorem homogeneousModel_feeding_original (net : AffineSkipNetwork N h₁ h₂)
    (j : Fin h₁) (hj : (homogeneousModel net).Feeding j) :
    ∃ k,net.W k j≠0 := by
  exact (homogeneousExtension net).localize_feeding_original _ _ j hj

/-- The local equation is exact for all sufficiently small positive steps,
and is not an approximation or a differentiability assumption. -/
theorem homogeneousModel_exact_direction (net : AffineSkipNetwork N h₁ h₂) (x : Point N) :
    ∃ ε : ℝ,0<ε ∧ eval net (ε • x)=eval net 0+ε*(homogeneousModel net).eval x := by
  obtain ⟨ε,hε,he⟩ := (homogeneousExtension net).exists_eval_direction
    (constantPoint N) (originalCoordinates N) x
  refine ⟨ε,hε,?_⟩
  rw [affinePoint_step,homogeneousExtension_eval] at he
  have hbase : (homogeneousExtension net).eval (constantPoint N)=eval net 0 :=
    homogeneousExtension_eval net 0
  rw [hbase,←localize_eval] at he
  exact he

/-- The actual all-real MAX equation alone yields a homogeneous model with
exactly the original two hidden-layer index types. -/
theorem homogeneousModel_computes_max [NeZero N] (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x,eval net x=Maximum N x) :
    ∀ x,(homogeneousModel net).eval x=Maximum N x := by
  intro x
  obtain ⟨ε,hε,he⟩ := homogeneousModel_exact_direction net x
  rw [hnet,hnet,Maximum_zero,zero_add,Maximum_smul hε] at he
  exact mul_left_cancel₀ hε.ne' he.symm

#check @homogeneousModel_computes_max
#print axioms homogeneousExtension_eval
#print axioms homogeneousModel_exact_direction
#print axioms homogeneousModel_computes_max
end MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
