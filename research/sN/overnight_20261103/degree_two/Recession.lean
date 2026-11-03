import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model

/-! Bias removal for the primitive nine-array affine-skip model.

The result keeps every original coefficient and both hidden-layer index
types. In particular parallel first-row cancellations are not disturbed by
discarding rows with nonzero original biases. The existing ordinary-network
bias theorem is used through its proved exact encoding, only to establish
the function identity; the returned network has the original widths.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DegreeTwo.Recession
open BigOperators Frontier Frontier.RandomRestriction
open AffineSkipExtension
variable {N h₁ h₂ : ℕ}

/-- Set only the three bias arrays to zero. -/
def zeroBias (net : AffineSkipNetwork N h₁ h₂) : AffineSkipNetwork N h₁ h₂ where
  A := net.A
  b := 0
  W := net.W
  U := net.U
  θ := 0
  d := net.d
  B := net.B
  L := net.L
  β := 0

/-- The exact encoding commutes with bias removal. -/
theorem encode_zeroBias (net : AffineSkipNetwork N h₁ h₂) :
    encode (zeroBias net) = (encode net).zeroBias := by
  unfold encode Network.zeroBias zeroBias
  congr 1
  · funext j
    rcases (firstIndexEquiv N h₁).symm j with (j|i)|i <;> rfl
  · funext k
    simp only [expandedOuterBias, Pi.zero_apply, neg_zero, ite_self]
    cases (outerIndexEquiv h₂).symm k <;> rfl

/-- Bias removal preserves any exactly represented positively homogeneous
target, with no support, sign, normalization, or width assumptions. -/
theorem zeroBias_eval_of_posHom (net : AffineSkipNetwork N h₁ h₂)
    (f : Point N → ℝ)
    (hf : ∀ c : ℝ, 0<c → ∀ x, f (c • x)=c*f x)
    (hnet : ∀ x, AffineSkipExtension.eval net x=f x) :
    ∀ x, AffineSkipExtension.eval (zeroBias net) x=f x := by
  have henc : ∀ x, (encode net).eval x=f x :=
    fun x => (encode_eval net x).trans (hnet x)
  have hz := (encode net).eval_zeroBias_of_posHom f hf henc
  intro x
  rw [←encode_eval, encode_zeroBias]
  exact hz x

/-- Homogeneous model with exactly the original six non-bias arrays. -/
def model (net : AffineSkipNetwork N h₁ h₂) : NormalizedNetwork N h₁ h₂ where
  A := net.A
  U := net.U
  W := net.W
  L := net.L
  B := net.B
  d := net.d

theorem model_eval (net : AffineSkipNetwork N h₁ h₂) (x : Point N) :
    (model net).eval x=AffineSkipExtension.eval (zeroBias net) x := by
  simp only [NormalizedNetwork.eval,NormalizedNetwork.inner,model,
    AffineSkipExtension.eval,outputSkip,AffineSkipExtension.inner,first,zeroBias,
    Pi.zero_apply,add_zero,lin]
  simp only [add_comm,add_left_comm,add_assoc]

theorem model_computes_posHom (net : AffineSkipNetwork N h₁ h₂)
    (f : Point N → ℝ)
    (hf : ∀ c : ℝ, 0<c → ∀ x, f (c • x)=c*f x)
    (hnet : ∀ x, AffineSkipExtension.eval net x=f x) :
    ∀ x, (model net).eval x=f x :=
  fun x => (model_eval net x).trans (zeroBias_eval_of_posHom net f hf hnet x)

/-- An actual all-input MAX identity yields an exact model with unchanged
first covectors, second matrix, skips, output weights, and hidden widths. -/
theorem model_computes_max [NeZero N] (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, AffineSkipExtension.eval net x=Maximum N x) :
    ∀ x, (model net).eval x=Maximum N x :=
  model_computes_posHom net (Maximum N) (fun c hc x => Maximum_smul hc x) hnet

#check @model_computes_max
#check @model_computes_posHom
#print axioms encode_zeroBias
#print axioms zeroBias_eval_of_posHom
#print axioms model_eval
#print axioms model_computes_max
end MaxCaterpillar.ExponentialPush.DegreeTwo.Recession
