import research.sN.exponential_push_20261102.structural.ActualBraidGraph
import research.sN.exponential_push_20261102.ridge_annihilator.RankBridge
import MaxCaterpillar.Frontier.SecondWidthN
import Mathlib.Combinatorics.SimpleGraph.Connectivity

/-! Every exact normalized braid representation of MAX has an original active
second unit whose actual signed interaction graph has at most two components.
The argument uses periods, so cancellations between parallel rows are retained. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork

variable {N h₁ h₂ : ℕ}

lemma component_rep (G : SimpleGraph (Fin N)) (c : G.ConnectedComponent) :
    ∃ v, G.connectedComponentMk v = c := by
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v => exact ⟨v,rfl⟩

/-- Three components permit a component-constant, non-diagonal direction
annihilating any one linear head. No normalization of the head is required. -/
theorem exists_component_constant_kernel (G : SimpleGraph (Fin N))
    (hG : 2 < Nat.card G.ConnectedComponent) (H : Point N) :
    ∃ v : Point N, lin H v = 0 ∧ (∃ i j, v i ≠ v j) ∧
      ∀ a b, G.Adj a b → v a = v b := by
  classical
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hcard : 2 < Fintype.card G.ConnectedComponent := by
    simpa only [Nat.card_eq_fintype_card] using hG
  obtain ⟨c₀,c₁,c₂,h01,h02,h12⟩ := Fintype.two_lt_card_iff.mp hcard
  obtain ⟨i₀,hi₀⟩ := component_rep G c₀
  obtain ⟨i₁,hi₁⟩ := component_rep G c₁
  obtain ⟨i₂,hi₂⟩ := component_rep G c₂
  let e₀ : Point N := fun i => if G.connectedComponentMk i=c₀ then 1 else 0
  let e₁ : Point N := fun i => if G.connectedComponentMk i=c₁ then 1 else 0
  have he₀ : ∀ a b, G.Adj a b → e₀ a=e₀ b := by
    intro a b hab
    dsimp [e₀]
    rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab]
  have he₁ : ∀ a b, G.Adj a b → e₁ a=e₁ b := by
    intro a b hab
    dsimp [e₁]
    rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab]
  by_cases hzero : lin H e₀=0
  · refine ⟨e₀,hzero,⟨i₀,i₂,?_⟩,he₀⟩
    simp [e₀,hi₀,hi₂,Ne.symm h02]
  · refine ⟨lin H e₁ • e₀ - lin H e₀ • e₁,?_,⟨i₁,i₂,?_⟩,?_⟩
    · rw [lin_sub_right,lin_smul_right,lin_smul_right]
      ring
    · simpa [e₀,e₁,hi₁,hi₂,Ne.symm h01,Ne.symm h02,Ne.symm h12] using
        neg_ne_zero.mpr hzero
    · intro a b hab
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,he₀ a b hab,he₁ a b hab]

/-- A component-constant direction annihilating the corrected head is an
actual period of the original second preactivation. -/
theorem inner_period_of_components (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2) (k : Fin h₂)
    (v : Point N)
    (hhead : lin (ExponentialPush.ActualBraid.head (net.U k) net.A (net.W k)) v=0)
    (hconst : ∀ a b,(braidInteractionGraph net hn k).Adj a b → v a=v b)
    (x : Point N) : net.inner k (x+v)=net.inner k x := by
  classical
  rw [NormalizedNetwork.inner,NormalizedNetwork.inner,
    ExponentialPush.ActualBraid.linear_combination_canonical _ _ _ hn.1 hbraid,
    ExponentialPush.ActualBraid.linear_combination_canonical _ _ _ hn.1 hbraid,
    lin_add_right,hhead,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : ExponentialPush.ActualBraid.coefficient net.A (net.W k) p=0
  · simp only [hp,zero_mul]
  · have he : (braidInteractionGraph net hn k).Adj
        (ExponentialPush.ActualBraid.left p) (ExponentialPush.ActualBraid.right p) := by
      refine ⟨ExponentialPush.ActualBraid.pair_distinct p,?_⟩
      rw [ExponentialPush.ActualBraid.coefficient_eq_original] at hp
      exact neg_ne_zero.mp hp
    have hv := hconst _ _ he
    simp only [Pi.add_apply]
    congr 2
    linarith only [hv]

/-- The graph and the second-neuron index are both those of the given network;
no uncancelled union of first-row supports is substituted. -/
theorem exists_active_second_two_components [NeZero N] (hN : 3≤N)
    (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized)
    (hbraid : ∀ j,(rowSupport (net.A j)).card≤2)
    (hmax : ∀ x,net.eval x=Maximum N x) :
    ∃ k : Fin h₂,net.d k≠0 ∧
      Nat.card (braidInteractionGraph net hn k).ConnectedComponent≤2 := by
  classical
  by_contra! hbad
  have hN2 : 2≤N := (by norm_num : 2≤3).trans hN
  have hscalar : FiniteDimensional.finrank ℝ ℝ≤N-2 := by
    rw [FiniteDimensional.finrank_self]
    exact (Nat.le_sub_iff_add_le hN2).mpr hN
  let f : Fin h₁ ⊕ Fin h₂ → Point N → ℝ :=
    Sum.elim (fun j x => net.B j*relu (lin (net.A j) x))
      (fun k x => net.d k*relu (net.inner k x))
  have hf : ∀ s,∃ v : Point N,(∃ i j,v i≠v j) ∧ ∀ x,f s (x+v)=f s x := by
    intro s
    rcases s with j|k
    · obtain ⟨v,hv,hnd⟩ := ExponentialPush.Ridge.exists_nondiagonal_ker_of_finrank
        hN2 (linMap (net.A j)) hscalar
      refine ⟨v,hnd,?_⟩
      intro x
      change net.B j*relu (lin (net.A j) (x+v))=net.B j*relu (lin (net.A j) x)
      change lin (net.A j) v=0 at hv
      rw [lin_add_right,hv,add_zero]
    · by_cases hd : net.d k=0
      · obtain ⟨v,_,hnd⟩ := ExponentialPush.Ridge.exists_nondiagonal_ker_of_finrank
          hN2 (0 : Point N →ₗ[ℝ] ℝ) hscalar
        refine ⟨v,hnd,?_⟩
        intro x
        change net.d k*relu (net.inner k (x+v))=net.d k*relu (net.inner k x)
        simp only [hd,zero_mul]
      · obtain ⟨v,hv,hnd,hconst⟩ := exists_component_constant_kernel
          (braidInteractionGraph net hn k) (hbad k hd)
          (ExponentialPush.ActualBraid.head (net.U k) net.A (net.W k))
        refine ⟨v,hnd,?_⟩
        intro x
        change net.d k*relu (net.inner k (x+v))=net.d k*relu (net.inner k x)
        rw [inner_period_of_components net hn hbraid k v hv hconst x]
  apply ExponentialPush.Ridge.maximum_ne_affine_sum_of_exists_periods hN2 f hf
    (linMap net.L).toAddMonoidHom 0
  intro x
  rw [←hmax x]
  simp only [f,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,eval,
    AddMonoidHom.coe_coe,add_zero]
  change lin net.L x+(∑ j,net.B j*relu (lin (net.A j) x))+
      ∑ k,net.d k*relu (net.inner k x)=
    lin net.L x+((∑ j,net.B j*relu (lin (net.A j) x))+
      ∑ k,net.d k*relu (net.inner k x))
  ring

#print axioms exists_component_constant_kernel
#print axioms inner_period_of_components
#print axioms exists_active_second_two_components
end MaxCaterpillar.Overnight.DegreeTwo

namespace MaxCaterpillar.ExponentialPush.DegreeTwo
open Frontier Frontier.RandomRestriction NormalizedNetwork
/-- Compatibility facade for the selected-tie counting development. -/
theorem exists_active_second_le_two_components {N h₁ h₂ : ℕ} [NeZero N]
    (hN : 3≤N) (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized)
    (hcard : ∀ j,(rowSupport (net.A j)).card≤2)
    (hmax : ∀ x,net.eval x=Maximum N x) :
    ∃ k : Fin h₂,net.d k≠0 ∧
      Nat.card (braidInteractionGraph net hn k).ConnectedComponent≤2 :=
  Overnight.DegreeTwo.exists_active_second_two_components hN net hn hcard hmax
#print axioms exists_active_second_le_two_components
end MaxCaterpillar.ExponentialPush.DegreeTwo
