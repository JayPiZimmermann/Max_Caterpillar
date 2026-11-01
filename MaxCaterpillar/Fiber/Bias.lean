import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Fiber.Retraction
import MaxCaterpillar.Frontier.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Connected.PathConnected

/-! # Removing biases through exact representations

For a positively homogeneous target, multiplying every bias in an exact network by
the same nonnegative scalar preserves its function. For the maximum target this
gives a strong deformation retraction from the exact fiber to its zero-bias
subspace. These statements use the actual parameter topology and all-input equality.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Fiber

open Frontier unitInterval

variable {N h₁ h₂ : ℕ}

/-- Common nonnegative bias scaling preserves any positively homogeneous target. -/
theorem scaleBias_eval_of_posHom (net : Network N h₁ h₂) (f : Point N → ℝ)
    (hf : ∀ c : ℝ, 0 < c → ∀ x, f (c • x) = c * f x)
    (h : ∀ x, net.eval x = f x) {c : ℝ} (hc : 0 ≤ c) :
    ∀ x, (net.scaleBias c).eval x = f x := by
  rcases eq_or_lt_of_le hc with hc | hc
  · subst c
    simpa only [Network.scaleBias, zero_smul, zero_mul, Network.zeroBias] using
      net.eval_zeroBias_of_posHom f hf h
  · intro x
    have hci : 0 < c⁻¹ := inv_pos.mpr hc
    have he := net.eval_smul hci x
    rw [inv_inv, h, hf _ hci] at he
    exact (mul_left_cancel₀ hci.ne' he).symm

@[simp] theorem scaleBias_zero (net : Network N h₁ h₂) :
    net.scaleBias 0 = net.zeroBias := by
  simp only [Network.scaleBias, Network.zeroBias, zero_smul, zero_mul]

@[simp] theorem scaleBias_one (net : Network N h₁ h₂) : net.scaleBias 1 = net := by
  cases net
  simp only [Network.scaleBias, one_smul, one_mul]

/-- Common bias scaling fixes every zero-bias network, even for arbitrary scalars. -/
theorem scaleBias_eq_self (net : Network N h₁ h₂) (h : net.HasZeroBiases) (c : ℝ) :
    net.scaleBias c = net := by
  rcases net with ⟨A, b, B, d, a, e⟩
  rcases h with ⟨hb, hd, he⟩
  dsimp at hb hd he
  subst b
  subst d
  subst e
  simp only [Network.scaleBias, smul_zero, mul_zero]

/-- Joint continuity, including the endpoint where every bias vanishes. -/
theorem continuous_scaleBias :
    Continuous (fun p : ℝ × Network N h₁ h₂ => p.2.scaleBias p.1) := by
  apply (continuous_network_iff _).mpr
  dsimp only [Network.scaleBias]
  exact ⟨continuous_W₁.comp continuous_snd,
    continuous_fst.smul (continuous_b₁.comp continuous_snd),
    continuous_W₂.comp continuous_snd,
    continuous_fst.smul (continuous_b₂.comp continuous_snd),
    continuous_w₃.comp continuous_snd,
    continuous_fst.mul (continuous_b₃.comp continuous_snd)⟩

theorem continuous_zeroBias :
    Continuous (fun net : Network N h₁ h₂ => net.zeroBias) := by
  simpa only [Function.comp_def, id_eq, scaleBias_zero] using
    (continuous_scaleBias.comp (continuous_const.prod_mk continuous_id) :
      Continuous (fun net : Network N h₁ h₂ => net.scaleBias (0 : ℝ)))

variable [NeZero N]

/-- The full exact maximum fiber restricted to zero bias parameters. -/
abbrev ZeroBiasFiber (N h₁ h₂ : ℕ) [NeZero N] :=
  {net : ExactFiber N h₁ h₂ // net.val.HasZeroBiases}

/-- Forget the zero-bias condition without changing any parameter. -/
def includeZeroBias : ZeroBiasFiber N h₁ h₂ → ExactFiber N h₁ h₂ := Subtype.val

/-- Erasing all biases, as a map of the exact fiber into itself. -/
def zeroBiasFiber (net : ExactFiber N h₁ h₂) : ExactFiber N h₁ h₂ :=
  ⟨net.val.zeroBias, net.val.eval_zeroBias_of_posHom (Maximum N)
    (fun c hc x => Maximum_smul hc x) net.property⟩

/-- The bias-removal retraction onto the zero-bias exact fiber. -/
def zeroBiasRetraction (net : ExactFiber N h₁ h₂) : ZeroBiasFiber N h₁ h₂ :=
  ⟨zeroBiasFiber net, net.val.zeroBias_hasZeroBiases⟩

theorem continuous_zeroBiasFiber : Continuous (zeroBiasFiber (N := N) (h₁ := h₁) (h₂ := h₂)) :=
  (continuous_zeroBias.comp continuous_subtype_val).subtype_mk _

theorem continuous_zeroBiasRetraction :
    Continuous (zeroBiasRetraction (N := N) (h₁ := h₁) (h₂ := h₂)) :=
  continuous_zeroBiasFiber.subtype_mk _

theorem continuous_includeZeroBias :
    Continuous (includeZeroBias (N := N) (h₁ := h₁) (h₂ := h₂)) :=
  continuous_subtype_val

@[simp] theorem zeroBiasRetraction_include (net : ZeroBiasFiber N h₁ h₂) :
    zeroBiasRetraction (includeZeroBias net) = net := by
  apply Subtype.ext
  apply Subtype.ext
  change net.val.val.zeroBias = net.val.val
  rw [← scaleBias_zero]
  exact scaleBias_eq_self _ net.property 0

/-- At time `t`, all biases are multiplied by `1-t`; no width is changed. -/
def biasDeformation (t : I) (net : ExactFiber N h₁ h₂) : ExactFiber N h₁ h₂ :=
  ⟨net.val.scaleBias (1 - (t : ℝ)),
    scaleBias_eval_of_posHom net.val (Maximum N)
      (fun c hc x => Maximum_smul hc x) net.property (sub_nonneg.mpr t.property.2)⟩

theorem continuous_biasDeformation :
    Continuous (fun p : I × ExactFiber N h₁ h₂ => biasDeformation p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_scaleBias.comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prod_mk
      (continuous_subtype_val.comp continuous_snd))

@[simp] theorem biasDeformation_zero (net : ExactFiber N h₁ h₂) :
    biasDeformation 0 net = net := by
  apply Subtype.ext
  change net.val.scaleBias (1 - ((0 : I) : ℝ)) = net.val
  simpa using scaleBias_one net.val

@[simp] theorem biasDeformation_one (net : ExactFiber N h₁ h₂) :
    biasDeformation 1 net = zeroBiasFiber net := by
  apply Subtype.ext
  change net.val.scaleBias (1 - ((1 : I) : ℝ)) = net.val.zeroBias
  simpa using scaleBias_zero net.val

theorem biasDeformation_fixed (t : I) (net : ExactFiber N h₁ h₂)
    (h : net.val.HasZeroBiases) : biasDeformation t net = net := by
  apply Subtype.ext
  exact scaleBias_eq_self net.val h _

/-- The bias-removal endpoint as a continuous self-map of the full fiber. -/
def zeroBiasContinuousMap : C(ExactFiber N h₁ h₂, ExactFiber N h₁ h₂) :=
  ⟨zeroBiasFiber, continuous_zeroBiasFiber⟩

/-- A strong deformation retraction: the homotopy fixes the zero-bias subspace. -/
def biasStrongDeformation :
    (ContinuousMap.id (ExactFiber N h₁ h₂)).HomotopyRel zeroBiasContinuousMap
      {net | net.val.HasZeroBiases} where
  toFun p := biasDeformation p.1 p.2
  continuous_toFun := continuous_biasDeformation
  map_zero_left := biasDeformation_zero
  map_one_left := biasDeformation_one
  prop' t net h := biasDeformation_fixed t net h

/-- Each exact network is joined to its zero-bias representative inside the exact fiber. -/
def biasPath (net : ExactFiber N h₁ h₂) : Path net (zeroBiasFiber net) where
  toFun t := biasDeformation t net
  continuous_toFun := continuous_biasDeformation.comp (continuous_id.prod_mk continuous_const)
  source' := biasDeformation_zero net
  target' := biasDeformation_one net

/-- Removing biases does not change the set of connected components of the full fiber. -/
noncomputable def zeroBiasConnectedComponentsEquiv :
    ConnectedComponents (ExactFiber N h₁ h₂) ≃ ConnectedComponents (ZeroBiasFiber N h₁ h₂) :=
  connectedComponentsEquivOfRetraction zeroBiasRetraction includeZeroBias
    continuous_zeroBiasRetraction continuous_includeZeroBias zeroBiasRetraction_include
    (fun net => pathComponent_subset_component net ⟨biasPath net⟩)

/-- The component bijection also preserves the quotient topologies on component spaces. -/
noncomputable def zeroBiasConnectedComponentsHomeomorph :
    ConnectedComponents (ExactFiber N h₁ h₂) ≃ₜ ConnectedComponents (ZeroBiasFiber N h₁ h₂) :=
  connectedComponentsHomeomorphOfRetraction zeroBiasRetraction includeZeroBias
    continuous_zeroBiasRetraction continuous_includeZeroBias zeroBiasRetraction_include
    (fun net => pathComponent_subset_component net ⟨biasPath net⟩)

end Fiber
end MaxCaterpillar
