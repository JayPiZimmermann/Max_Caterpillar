import research.sN.overnight_20261103.cycle_bridge.Equivalence

/-! Independent expanded contracts and concrete controls for the actual
cycle-to-forest network replacement. This file is a checker, not a consumer. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.CycleBridge.IndependentCheck
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open ActualBraid DictionaryBridge ForestMatching GrowingMatching
attribute [local instance] Classical.propDecidable

/-- The replacement conclusion is an ordinary finite indexed network. The
forest condition and all-input identity are conclusions, not assumptions. -/
theorem exact_replacement_contract {N h₁ h₂ : ℕ}
    (net : NormalizedNetwork N h₁ h₂)
    (hA : ∀ j,∑ i,net.A j i=0) (hU : ∀ k,∑ i,net.U k i=0)
    (hL : ∑ i,net.L i=1)
    (hs : ∀ j,(rowSupport (net.A j)).card≤2) :
    ∃ w₂ : ℕ, ∃ out : NormalizedNetwork N (Fintype.card (Pair N)) w₂,
      ∃ hn : out.TranslationNormalized,
      w₂≤h₂*3^Fintype.card (Pair N) ∧
      (∀ j,(rowSupport (out.A j)).card≤2) ∧
      (∀ x,out.eval x=net.eval x) ∧
      ∀ k,(braidInteractionGraph out hn k).IsAcyclic := by
  have hn : net.TranslationNormalized := ⟨hA,hU,hL⟩
  obtain ⟨d,hd⟩ := exists_expansion net hn hs
  let hnew := expanded_translationNormalized net hn hs d
  exact ⟨_,expandedNetwork net d,hnew,expanded_width_le net,
    expanded_support_le_two net d,hd,expanded_graph_acyclic net d hnew⟩

/-- Expanded cover exclusion at the same input arity is exactly the H(k,q)
structural premise used by the existing growing-matching counting theorem. -/
theorem exact_obstruction_contract (N r : ℕ) [NeZero N] :
    LocalMatchingObstruction N (r+1) ↔
    (∀ (h₁ h₂ : ℕ) (net : NormalizedNetwork N h₁ h₂)
      (hn : net.TranslationNormalized),
      (∀ j,(rowSupport (net.A j)).card≤2) →
      (∀ x,net.eval x=Maximum N x) →
      (∀ k : Fin h₂,∃ C : Finset (Fin N),
        (∀ a b,(braidInteractionGraph net hn k).Adj a b → a∈C ∨ b∈C) ∧
        C.card≤r) → False) := by
  rw [localMatchingObstruction_iff_no_cover_representation]
  constructor
  · intro H h₁ h₂ net hn hs he hC
    exact H ⟨h₁,h₂,net,hn,hs,he,hC⟩
  · intro H
    rintro ⟨h₁,h₂,net,hn,hs,he,hC⟩
    exact H h₁ h₂ net hn hs he hC

/-- A genuine original triangle with three nonzero comparison coefficients. -/
def triangleModel : NormalizedNetwork 3 3 1 where
  A := ![![1,-1,0],![0,1,-1],![1,0,-1]]
  U := fun _ => ![-3,0,3]
  W := fun _ _ => 1
  L := ![1,0,0]
  B := fun _ => 0
  d := fun _ => 1

theorem triangle_normalized : triangleModel.TranslationNormalized := by
  refine ⟨?_,?_,?_⟩
  · intro j
    fin_cases j <;> norm_num [triangleModel,Fin.sum_univ_succ]
  · intro k
    norm_num [triangleModel,Fin.sum_univ_succ]
  · norm_num [triangleModel,Fin.sum_univ_succ]

theorem triangle_row_support (j : Fin 3) :
    rowSupport (triangleModel.A j)= ![({0,1} : Finset (Fin 3)),{1,2},{0,2}] j := by
  fin_cases j <;> ext i <;> fin_cases i <;>
    norm_num [mem_rowSupport,triangleModel,Fin.ext_iff]

theorem triangle_support : ∀ j,(rowSupport (triangleModel.A j)).card≤2 := by
  intro j
  rw [triangle_row_support]
  fin_cases j <;> norm_num

theorem triangle_graph : braidInteractionGraph triangleModel triangle_normalized 0=⊤ := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  change (a≠b ∧ braidEdgeWeight triangleModel.A (triangleModel.W 0) a b≠0) ↔ a≠b
  simp only [braidEdgeWeight,braidEdgeRows,Finset.sum_filter,triangle_row_support]
  fin_cases a <;> fin_cases b <;>
    norm_num [triangleModel,Fin.sum_univ_succ,Finset.ext_iff,Fin.forall_fin_succ,Fin.ext_iff]

theorem triangle_source_nonacyclic :
    ¬(braidInteractionGraph triangleModel triangle_normalized 0).IsAcyclic := by
  rw [triangle_graph]
  let p : (⊤ : SimpleGraph (Fin 3)).Walk 0 0 :=
    .cons (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 from by decide)
      (.cons (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 from by decide)
        (.cons (show (⊤ : SimpleGraph (Fin 3)).Adj 2 0 from by decide) .nil))
  intro h
  apply h p
  norm_num [p,SimpleGraph.Walk.isCycle_def,SimpleGraph.Walk.isTrail_def,
    SimpleGraph.Walk.edges,SimpleGraph.Walk.darts,SimpleGraph.Dart.edge,
    SimpleGraph.Walk.support,Sym2.eq_iff]

/-- The outer gate of the cyclic control really changes sign. -/
theorem triangle_inner_sign_control :
    triangleModel.inner 0 ![1,0,0]= -1 ∧ triangleModel.inner 0 ![0,0,1]=3 := by
  norm_num [NormalizedNetwork.inner,triangleModel,lin,Fin.sum_univ_succ,relu]

/-- The nontrivial cyclic source network has an exact forest replacement
on all real inputs, with the advertised explicit finite width budget. -/
theorem triangle_replacement :
    ∃ w₂ : ℕ,∃ out : NormalizedNetwork 3 (Fintype.card (Pair 3)) w₂,
      ∃ hn : out.TranslationNormalized,
      w₂≤3^Fintype.card (Pair 3) ∧
      (∀ x,out.eval x=triangleModel.eval x) ∧
      ∀ k,(braidInteractionGraph out hn k).IsAcyclic := by
  obtain ⟨w₂,out,hn,hw,_,he,hg⟩ := exact_replacement_contract triangleModel
    triangle_normalized.1 triangle_normalized.2.1 triangle_normalized.2.2 triangle_support
  exact ⟨w₂,out,hn,by simpa using hw,he,hg⟩

/-- The one-input maximum has an actual empty-hidden-layer normalized
representation. Neither finite indexing nor the equivalence hides an
inhabited hidden-layer hypothesis. -/
def emptyModel : NormalizedNetwork 1 0 0 where
  A := fun j => Fin.elim0 j
  U := fun k => Fin.elim0 k
  W := fun k => Fin.elim0 k
  L := fun _ => 1
  B := fun j => Fin.elim0 j
  d := fun k => Fin.elim0 k

theorem empty_cover_control : CoverRepresentable 1 0 (Maximum 1) := by
  let net := emptyModel
  have hn : net.TranslationNormalized := by
    refine ⟨?_,?_,?_⟩
    · intro j
      exact Fin.elim0 j
    · intro k
      exact Fin.elim0 k
    · norm_num [net,emptyModel,Fin.sum_univ_succ]
  refine ⟨0,0,net,hn,?_,?_,?_⟩
  · intro j
    exact Fin.elim0 j
  · intro x
    have he : net.eval x=x 0 := by
      simp [net,emptyModel,NormalizedNetwork.eval,lin,Fin.sum_univ_succ]
    rw [he]
    apply le_antisymm
    · exact le_Maximum x 0
    · apply (Maximum_le_iff _ _).mpr
      intro i
      have hi : i=(0:Fin 1) := Subsingleton.elim i 0
      simp [hi]
  · intro k
    exact Fin.elim0 k

theorem one_input_obstruction_false : ¬LocalMatchingObstruction 1 1 := by
  intro h
  exact (localMatchingObstruction_iff_no_cover_representation 1 0).mp h empty_cover_control

#check @exact_replacement_contract
#check @exact_obstruction_contract
#print axioms exact_replacement_contract
#print axioms exact_obstruction_contract
#print axioms triangle_normalized
#print axioms triangle_graph
#print axioms triangle_source_nonacyclic
#print axioms triangle_inner_sign_control
#print axioms triangle_replacement
#print axioms empty_cover_control
#print axioms one_input_obstruction_false
end MaxCaterpillar.ExponentialPush.CycleBridge.IndependentCheck
