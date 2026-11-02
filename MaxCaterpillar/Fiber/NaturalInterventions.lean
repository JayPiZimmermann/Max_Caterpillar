import MaxCaterpillar.Frontier.Main
import MaxCaterpillar.Fiber.Basic
import Mathlib.Topology.Connected.PathConnected

/-!
# Equal natural activations do not determine neuron-interchange responses

An explicit pair of ordinary minimal-width Max4 networks has the same natural
activation maps at both hidden layers on every real input. Replacing one first
hidden activation by its value on another real input distinguishes the networks.
All activation and intervention definitions are evaluated from the six-array
`Network` model; the patched state is followed by the actual second layer.
-/

set_option autoImplicit false

namespace MaxCaterpillar
open BigOperators

namespace Network
variable {N h₁ h₂ : ℕ}

/-- The actual first hidden activation vector of the physical network. -/
noncomputable def firstHidden (net : Network N h₁ h₂) (x : Point N) : Fin h₁ → ℝ :=
  fun j => relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)

/-- The actual second hidden activation vector on a natural input. -/
noncomputable def secondHidden (net : Network N h₁ h₂) (x : Point N) : Fin h₂ → ℝ :=
  fun k => relu ((∑ j, net.W₂ k j * net.firstHidden x j) + net.b₂ k)

/-- Recompute the physical suffix from a specified first hidden state. -/
noncomputable def fromFirstHidden (net : Network N h₁ h₂) (z : Fin h₁ → ℝ) : ℝ :=
  (∑ k, net.w₃ k * relu ((∑ j, net.W₂ k j * z j) + net.b₂ k)) + net.b₃

/-- Ordinary one-neuron interchange, using a natural donor input. -/
noncomputable def interchangeFirst (net : Network N h₁ h₂)
    (base donor : Point N) (j : Fin h₁) : ℝ :=
  net.fromFirstHidden (Function.update (net.firstHidden base) j (net.firstHidden donor j))

lemma eval_eq_fromFirstHidden (net : Network N h₁ h₂) (x : Point N) :
    net.eval x = net.fromFirstHidden (net.firstHidden x) := rfl

lemma eval_eq_secondHidden (net : Network N h₁ h₂) (x : Point N) :
    net.eval x = (∑ k, net.w₃ k * net.secondHidden x k) + net.b₃ := rfl
end Network

namespace Fiber.NaturalInterventions
open Frontier

/-- The inactive first-layer coefficient is `-t`; all biases vanish. -/
noncomputable def net (t : ℝ) : Network 4 6 3 where
  W₁ := maxFourNet.W₁
  b₁ := 0
  W₂ := ![![0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, -t, 1], ![1,-1,1,-1,-1,1]]
  b₂ := 0
  w₃ := ![1,-1,1]
  b₃ := 0

lemma net_zeroBiases (t : ℝ) : (net t).HasZeroBiases := ⟨rfl,rfl,rfl⟩

lemma firstHidden_net (t : ℝ) (x : Point 4) :
    (net t).firstHidden x =
      ![relu (x 0-x 1), relu (x 2-x 3), relu (x 1), relu (-x 1),
        relu (x 3), relu (-x 3)] := by
  funext j
  fin_cases j <;>
    simp [Network.firstHidden, net, maxFourNet, Fin.sum_univ_succ, sub_eq_add_neg] <;> rfl

private lemma inactive_term (t z : ℝ) (ht : 0 ≤ t) :
    relu (-t * relu z + relu (-z)) = relu (-z) := by
  rcases le_total 0 z with hz | hz
  · rw [relu_of_nonneg hz, relu_of_nonpos (neg_nonpos.mpr hz)]
    apply relu_of_nonpos
    nlinarith
  · rw [relu_of_nonpos hz, mul_zero, zero_add, relu_relu]

lemma secondHidden_net (t : ℝ) (ht : 0 ≤ t) (x : Point 4) :
    (net t).secondHidden x =
      ![relu (x 2-x 3)+relu (x 3), relu (-x 3),
        relu (relu (x 0-x 1)-relu (x 2-x 3)+relu (x 1)-relu (-x 1)-relu (x 3)+relu (-x 3))] := by
  unfold Network.secondHidden
  rw [firstHidden_net]
  funext k
  fin_cases k
  · norm_num [net, Fin.sum_univ_succ]
    exact relu_of_nonneg (add_nonneg (relu_nonneg _) (relu_nonneg _))
  · simpa [net, Fin.sum_univ_succ] using inactive_term t (x 3) ht
  · simp [net, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc]

/-- All members of the half-line family have identical natural hidden maps. -/
theorem same_natural_hidden (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∀ x, (net s).firstHidden x = (net t).firstHidden x) ∧
      (∀ x, (net s).secondHidden x = (net t).secondHidden x) := by
  constructor
  · intro x
    rw [firstHidden_net, firstHidden_net]
  · intro x
    rw [secondHidden_net s hs, secondHidden_net t ht]

/-- Every network in the family computes Max4 on all real inputs. -/
theorem net_eval (t : ℝ) (ht : 0 ≤ t) (x : Point 4) : (net t).eval x = Maximum 4 x := by
  rw [Network.eval_eq_secondHidden, secondHidden_net t ht, Maximum_four]
  simp only [net, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ, Matrix.cons_val_two,
    Matrix.tail_cons, Pi.zero_apply, one_mul, neg_mul, add_zero, zero_add,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  have ha : relu (x 0-x 1)+relu (x 1)-relu (-x 1) = max (x 0) (x 1) := by
    have h := relu_sub_add (x 1) (x 0)
    rw [max_comm] at h
    linarith [relu_sub_relu_neg (x 1)]
  have hb : relu (x 2-x 3)+relu (x 3)-relu (-x 3) = max (x 2) (x 3) := by
    have h := relu_sub_add (x 3) (x 2)
    rw [max_comm] at h
    linarith [relu_sub_relu_neg (x 3)]
  have hd : relu (x 0-x 1)-relu (x 2-x 3)+relu (x 1)-relu (-x 1)-relu (x 3)+relu (-x 3) =
      max (x 0) (x 1)-max (x 2) (x 3) := by linarith only [ha,hb]
  rw [hd]
  have hf := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  rw [max_comm (max (x 2) (x 3)) (max (x 0) (x 1))] at hf
  linarith only [hb,hf]

/-- A natural base input at which the positive x3 gate is inactive. -/
def base : Point 4 := ![0,0,-1,-1]

/-- A real donor input whose positive x3 gate equals one. -/
def donor : Point 4 := ![0,0,0,1]

lemma patched_state (t : ℝ) :
    Function.update ((net t).firstHidden base) 4 ((net t).firstHidden donor 4) =
      ![0,0,0,0,1,1] := by
  have hb : (net t).firstHidden base = ![0,0,0,0,0,1] := by
    rw [firstHidden_net]
    change ![relu (0-0), relu ((-1)-(-1)), relu 0, relu (-0),
      relu (-1), relu (-(-1))] = ![0,0,0,0,0,1]
    norm_num [relu]
  have hd : (net t).firstHidden donor = ![0,0,0,0,1,0] := by
    rw [firstHidden_net]
    change ![relu (0-0), relu (0-1), relu 0, relu (-0), relu 1,
      relu (-1)] = ![0,0,0,0,1,0]
    norm_num [relu]
  rw [hb,hd]
  change Function.update (![0,0,0,0,0,1] : Fin 6 → ℝ) ⟨4,by decide⟩ 1 = ![0,0,0,0,1,1]
  funext j
  fin_cases j <;> norm_num [Function.update, Fin.ext_iff]

lemma interchange_zero : (net 0).interchangeFirst base donor 4 = 0 := by
  unfold Network.interchangeFirst
  rw [patched_state]
  norm_num [Network.fromFirstHidden, net, Fin.sum_univ_succ, relu]

lemma interchange_one : (net 1).interchangeFirst base donor 4 = 1 := by
  unfold Network.interchangeFirst
  rw [patched_state]
  norm_num [Network.fromFirstHidden, net, Fin.sum_univ_succ, relu]

/-- Identical all-input natural activations, but different ordinary interchange
responses, in a pair of ordinary zero-bias networks of minimal Max4 widths. -/
theorem natural_activation_counterexample :
    ∃ (a b : Network 4 6 3) (x y : Point 4) (j : Fin 6),
      a.HasZeroBiases ∧ b.HasZeroBiases ∧
      (∀ z, a.eval z = Maximum 4 z) ∧ (∀ z, b.eval z = Maximum 4 z) ∧
      (∀ z, a.firstHidden z = b.firstHidden z) ∧
      (∀ z, a.secondHidden z = b.secondHidden z) ∧
      a.interchangeFirst x y j = 0 ∧ b.interchangeFirst x y j = 1 := by
  obtain ⟨hfirst,hsecond⟩ := same_natural_hidden 0 1 (by norm_num) (by norm_num)
  exact ⟨net 0,net 1,base,donor,4,net_zeroBiases 0,net_zeroBiases 1,
    net_eval 0 (by norm_num),net_eval 1 (by norm_num),hfirst,hsecond,
    interchange_zero,interchange_one⟩

/-- The parameter family is continuous in the ordinary topology of all six arrays. -/
theorem continuous_net : Continuous net := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const, continuous_const, ?_, continuous_const,
    continuous_const, continuous_const⟩
  apply continuous_pi
  intro k
  apply continuous_pi
  intro j
  fin_cases k <;> fin_cases j <;>
    simp only [net, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.tail_cons] <;> continuity

/-- The two concrete endpoints in the full all-input exact parameter fiber. -/
noncomputable def zeroExact : ExactFiber 4 6 3 := ⟨net 0, net_eval 0 (by norm_num)⟩
noncomputable def oneExact : ExactFiber 4 6 3 := ⟨net 1, net_eval 1 (by norm_num)⟩

open unitInterval

/-- An explicit continuous exact path, with parameter t in [0,1]. -/
noncomputable def exactPath : Path zeroExact oneExact where
  toFun t := ⟨net (t : ℝ), net_eval (t : ℝ) t.property.1⟩
  continuous_toFun := (continuous_net.comp continuous_subtype_val).subtype_mk _
  source' := by apply Subtype.ext; rfl
  target' := by apply Subtype.ext; rfl

/-- Both natural hidden activation maps stay fixed along the whole exact path. -/
theorem exactPath_hidden_fixed (s t : I) :
    (∀ x, (exactPath s).val.firstHidden x = (exactPath t).val.firstHidden x) ∧
      (∀ x, (exactPath s).val.secondHidden x = (exactPath t).val.secondHidden x) :=
  same_natural_hidden (s : ℝ) (t : ℝ) s.property.1 t.property.1

/-- The endpoints lie in the same connected component of the full exact fiber. -/
theorem same_exact_component :
    ConnectedComponents.mk zeroExact = ConnectedComponents.mk oneExact :=
  ConnectedComponents.coe_eq_coe'.2
    (pathComponent_subset_component _ (show Joined zeroExact oneExact from ⟨exactPath⟩).symm)

/-- Even within one path component of the full exact fiber, identical natural
hidden activation maps need not preserve ordinary neuron-interchange responses. -/
theorem connected_natural_activation_counterexample :
    ∃ a b : ExactFiber 4 6 3,
      Joined a b ∧ a.val.HasZeroBiases ∧ b.val.HasZeroBiases ∧
      (∀ z, a.val.firstHidden z = b.val.firstHidden z) ∧
      (∀ z, a.val.secondHidden z = b.val.secondHidden z) ∧
      a.val.interchangeFirst base donor 4 = 0 ∧
      b.val.interchangeFirst base donor 4 = 1 := by
  obtain ⟨hfirst,hsecond⟩ := same_natural_hidden 0 1 (by norm_num) (by norm_num)
  exact ⟨zeroExact,oneExact,⟨exactPath⟩,net_zeroBiases 0,net_zeroBiases 1,
    hfirst,hsecond,interchange_zero,interchange_one⟩

/-- No width smaller in either coordinate can compute Max4, even with biases. -/
theorem widths_minimal {h₁ h₂ : ℕ} (a : Network 4 h₁ h₂)
    (ha : ∀ x, a.eval x = Maximum 4 x) : 6 ≤ h₁ ∧ 3 ≤ h₂ :=
  max4_widths_iff.mp ⟨a,ha⟩

end Fiber.NaturalInterventions
end MaxCaterpillar
