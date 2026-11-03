import research.sN.overnight_20261103.degree_two.FourControl

/-! Independent degree check on the literal four-input model. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo.Audit
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open Check
attribute [local instance] Classical.propDecidable

@[simp] lemma fin_four_three_val : ((3 : Fin 4) : ℕ)=3 := rfl

lemma fourNet_support_zero : rowSupport (fourNet.A 0)={0,1} := by
  ext i
  fin_cases i <;> norm_num [rowSupport,fourNet,unitVec,Fin.ext_iff,Fin.coe_ofNat_eq_mod]

lemma fourNet_support_one : rowSupport (fourNet.A 1)={2,3} := by
  ext i
  fin_cases i <;> norm_num [rowSupport,fourNet,unitVec,Fin.ext_iff,Fin.coe_ofNat_eq_mod]

theorem fourNet_graph_edges (k : Fin 1) (a b : Fin 4) :
    (braidInteractionGraph fourNet fourNet_normalized k).Adj a b ↔
      (a=0 ∧ b=1) ∨ (a=1 ∧ b=0) ∨ (a=2 ∧ b=3) ∨ (a=3 ∧ b=2) := by
  rw [braidInteractionGraph_adj]
  simp only [braidEdgeWeight,braidEdgeRows,Finset.sum_filter,Fin.sum_univ_two,
    fourNet_support_zero,fourNet_support_one]
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    norm_num [fourNet,unitVec,Finset.ext_iff,Fin.forall_fin_succ,Fin.ext_iff,Fin.coe_ofNat_eq_mod]

theorem fourNet_degree (k : Fin 1) (a : Fin 4) :
    (braidInteractionGraph fourNet fourNet_normalized k).degree a≤1 := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hu' := (fourNet_graph_edges k a u).mp
    ((SimpleGraph.mem_neighborFinset _ _ _).mp hu)
  have hv' := (fourNet_graph_edges k a v).mp
    ((SimpleGraph.mem_neighborFinset _ _ _).mp hv)
  rcases hu' with ⟨h0,hu⟩|⟨h1,hu⟩|⟨h2,hu⟩|⟨h3,hu⟩ <;>
    rcases hv' with ⟨g0,hv⟩|⟨g1,hv⟩|⟨g2,hv⟩|⟨g3,hv⟩ <;>
    subst_vars <;> norm_num [Fin.ext_iff,Fin.coe_ofNat_eq_mod] at *

#check @fourNet_degree
#print axioms fourNet_graph_edges
#print axioms fourNet_degree
end MaxCaterpillar.Overnight.DegreeTwo.Audit
