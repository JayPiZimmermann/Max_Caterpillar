import research.sN.exponential_push_20261102.forest_matching.Cycle

set_option autoImplicit false
open BigOperators
namespace MaxCaterpillar.ExponentialPush.ForestMatching.Check

/-- The direct declaration audit spells out all hypotheses and all output
quantifiers, including a single orientation that works for every real input. -/
theorem exact_cycle_type {V ι : Type*} [DecidableEq V] [DecidableEq ι]
    (A : Finset ι) (a b : ι→V)
    (hcycle : ¬(indexedGraph A a b).IsAcyclic) :
    ∃ S : Finset ι, S⊆A ∧ S.Nonempty ∧ ∃ reverse : ι→Bool,
      ∀ x : V→ℝ,
        ∑ i in S,(if reverse i then -(x (a i)-x (b i)) else x (a i)-x (b i))=0 :=
  indexedGraph_oriented_cycle A a b hcycle

def triangle : SimpleGraph (Fin 3) := ⊤

def triangleWalk : triangle.Walk 0 0 :=
  .cons (show triangle.Adj 0 1 from by change (0:Fin 3)≠1; decide)
    (.cons (show triangle.Adj 1 2 from by change (1:Fin 3)≠2; decide)
      (.cons (show triangle.Adj 2 0 from by change (2:Fin 3)≠0; decide) .nil))

theorem triangle_nonacyclic : ¬triangle.IsAcyclic := by
  intro h
  exact h triangleWalk (by
    norm_num [triangleWalk,SimpleGraph.Walk.isCycle_def,SimpleGraph.Walk.isTrail_def,
      SimpleGraph.Walk.edges,SimpleGraph.Walk.darts,SimpleGraph.Dart.edge,
      SimpleGraph.Walk.support,Sym2.eq_iff]
    decide)

/-- Nonvacuity with a literal triangle and a redundant indexed dictionary
containing both orientations and loops. -/
theorem triangle_dictionary_control :
    ∃ S : Finset (Fin 3×Fin 3), S.Nonempty ∧ ∃ reverse : (Fin 3×Fin 3)→Bool,
      ∀ x : Fin 3→ℝ,
        ∑ i in S,(if reverse i then -(x i.1-x i.2) else x i.1-x i.2)=0 := by
  obtain ⟨S,_,hS,reverse,hr⟩ :=
    exists_oriented_cycle_of_not_acyclic triangle Finset.univ Prod.fst Prod.snd
      (fun v w _ => ⟨(v,w),Finset.mem_univ _,Or.inl ⟨rfl,rfl⟩⟩) triangle_nonacyclic
  exact ⟨S,hS,reverse,hr⟩

#check @indexedGraph_oriented_cycle
#print axioms exact_cycle_type
#print axioms triangle_nonacyclic
#print axioms triangle_dictionary_control

end MaxCaterpillar.ExponentialPush.ForestMatching.Check
