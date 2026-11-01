import MaxCaterpillar.Definitions
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Algebra.Ring.Basic

/-! # The all-input exact fiber with its parameter topology

The topology on the existing `Network` is the ordinary product topology on its
six real parameter arrays. `ExactFiber` is the subtype of networks computing the
maximum on every real input, with the subspace topology. No normal-form or
classification assumptions are built into these definitions.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Fiber

open BigOperators

/-- The six arrays of a network, with the ordinary real product topology. -/
abbrev ParameterSpace (N h₁ h₂ : ℕ) :=
  (Fin h₁ → Fin N → ℝ) × (Fin h₁ → ℝ) ×
    (Fin h₂ → Fin h₁ → ℝ) × (Fin h₂ → ℝ) × (Fin h₂ → ℝ) × ℝ

/-- The coefficient identification; it changes neither weights nor biases. -/
def networkEquivParameters (N h₁ h₂ : ℕ) :
    Network N h₁ h₂ ≃ ParameterSpace N h₁ h₂ where
  toFun net := ⟨net.W₁, net.b₁, net.W₂, net.b₂, net.w₃, net.b₃⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv net := by cases net; rfl
  right_inv p := by rcases p with ⟨a,b,c,d,e,f⟩; rfl

/-- Euclidean parameter topology, transported along the coefficient identification. -/
instance networkTopologicalSpace (N h₁ h₂ : ℕ) : TopologicalSpace (Network N h₁ h₂) :=
  TopologicalSpace.induced (networkEquivParameters N h₁ h₂) inferInstance

variable {N h₁ h₂ : ℕ}

theorem continuous_parameters :
    Continuous (networkEquivParameters N h₁ h₂) :=
  continuous_induced_dom

theorem continuous_W₁ : Continuous (fun net : Network N h₁ h₂ => net.W₁) :=
  continuous_fst.comp continuous_parameters

theorem continuous_b₁ : Continuous (fun net : Network N h₁ h₂ => net.b₁) :=
  continuous_fst.comp (continuous_snd.comp continuous_parameters)

theorem continuous_W₂ : Continuous (fun net : Network N h₁ h₂ => net.W₂) :=
  continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_parameters))

theorem continuous_b₂ : Continuous (fun net : Network N h₁ h₂ => net.b₂) :=
  continuous_fst.comp (continuous_snd.comp
    (continuous_snd.comp (continuous_snd.comp continuous_parameters)))

theorem continuous_w₃ : Continuous (fun net : Network N h₁ h₂ => net.w₃) :=
  continuous_fst.comp (continuous_snd.comp
    (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_parameters))))

theorem continuous_b₃ : Continuous (fun net : Network N h₁ h₂ => net.b₃) :=
  continuous_snd.comp (continuous_snd.comp
    (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_parameters))))

/-- Continuity of networks is precisely coordinatewise continuity of all six arrays. -/
theorem continuous_network_iff {X : Type*} [TopologicalSpace X]
    (f : X → Network N h₁ h₂) :
    Continuous f ↔
      Continuous (fun x => (f x).W₁) ∧ Continuous (fun x => (f x).b₁) ∧
      Continuous (fun x => (f x).W₂) ∧ Continuous (fun x => (f x).b₂) ∧
      Continuous (fun x => (f x).w₃) ∧ Continuous (fun x => (f x).b₃) := by
  constructor
  · intro h
    exact ⟨continuous_W₁.comp h, continuous_b₁.comp h,
      continuous_W₂.comp h, continuous_b₂.comp h,
      continuous_w₃.comp h, continuous_b₃.comp h⟩
  · rintro ⟨hW₁, hb₁, hW₂, hb₂, hw₃, hb₃⟩
    exact continuous_induced_rng.mpr
      (hW₁.prod_mk (hb₁.prod_mk (hW₂.prod_mk (hb₂.prod_mk (hw₃.prod_mk hb₃)))))

/-- The chosen topology is homeomorphic to the usual finite real product. -/
def networkHomeomorphParameters (N h₁ h₂ : ℕ) :
    Network N h₁ h₂ ≃ₜ ParameterSpace N h₁ h₂ where
  toEquiv := networkEquivParameters N h₁ h₂
  continuous_toFun := continuous_parameters
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using
      (continuous_id : Continuous (fun p : ParameterSpace N h₁ h₂ => p))

instance networkT2Space : T2Space (Network N h₁ h₂) :=
  T2Space.of_injective_continuous
    (networkEquivParameters N h₁ h₂).injective continuous_parameters

/-- Evaluation is jointly continuous when both parameters and inputs vary. -/
theorem continuous_network_eval {X : Type*} [TopologicalSpace X]
    {f : X → Network N h₁ h₂} {x : X → Point N}
    (hf : Continuous f) (hx : Continuous x) :
    Continuous (fun t => (f t).eval (x t)) := by
  unfold Network.eval
  refine (continuous_finset_sum _ fun k _ => ?_).add (continuous_b₃.comp hf)
  refine ((continuous_apply k).comp (continuous_w₃.comp hf)).mul ?_
  unfold relu
  refine continuous_const.max ?_
  refine (continuous_finset_sum _ fun j _ => ?_).add
    ((continuous_apply k).comp (continuous_b₂.comp hf))
  refine ((continuous_apply j).comp
    ((continuous_apply k).comp (continuous_W₂.comp hf))).mul ?_
  refine continuous_const.max ?_
  refine (continuous_finset_sum _ fun i _ => ?_).add
    ((continuous_apply j).comp (continuous_b₁.comp hf))
  exact ((continuous_apply i).comp ((continuous_apply j).comp (continuous_W₁.comp hf))).mul
    ((continuous_apply i).comp hx)

theorem continuous_eval (x : Point N) :
    Continuous (fun net : Network N h₁ h₂ => net.eval x) :=
  continuous_network_eval continuous_id continuous_const

theorem continuous_eval_joint :
    Continuous (fun p : Network N h₁ h₂ × Point N => p.1.eval p.2) :=
  continuous_network_eval continuous_fst continuous_snd

/-- Realization is continuous for the pointwise topology on real-valued functions. -/
theorem continuous_realization :
    Continuous (fun net : Network N h₁ h₂ => net.eval) :=
  continuous_pi fun x => continuous_eval x

/-- All-input exactness, including arbitrary real weights and arbitrary biases. -/
def ExactSet (N h₁ h₂ : ℕ) [NeZero N] : Set (Network N h₁ h₂) :=
  {net | ∀ x, net.eval x = Maximum N x}

/-- The exact fiber has the subspace topology of the full parameter space. -/
abbrev ExactFiber (N h₁ h₂ : ℕ) [NeZero N] := ↥(ExactSet N h₁ h₂)

@[simp] theorem mem_exactSet [NeZero N] (net : Network N h₁ h₂) :
    net ∈ ExactSet N h₁ h₂ ↔ ∀ x, net.eval x = Maximum N x := Iff.rfl

theorem isClosed_exactSet [NeZero N] : IsClosed (ExactSet N h₁ h₂) := by
  unfold ExactSet
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun x => isClosed_eq (continuous_eval x) continuous_const

theorem exactFiber_eval [NeZero N] (net : ExactFiber N h₁ h₂) (x : Point N) :
    net.val.eval x = Maximum N x := net.property x

theorem continuous_exactFiber_val [NeZero N] :
    Continuous (fun net : ExactFiber N h₁ h₂ => net.val) := continuous_subtype_val

theorem exactFiber_nonempty_iff [NeZero N] :
    Nonempty (ExactFiber N h₁ h₂) ↔
      ∃ net : Network N h₁ h₂, ∀ x, net.eval x = Maximum N x := by
  constructor
  · rintro ⟨net⟩
    exact ⟨net.val, net.property⟩
  · rintro ⟨net, hnet⟩
    exact ⟨⟨net, hnet⟩⟩

end Fiber
end MaxCaterpillar
