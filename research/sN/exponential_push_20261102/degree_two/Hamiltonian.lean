import research.sN.exponential_push_20261102.degree_two.PathUnique
import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic

/-! Research-only Hamiltonian paths in finite connected degree-two graphs. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.DegreeTwo
open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- There is a longest simple path in any nonempty finite graph. -/
theorem exists_longest_path [Nonempty V] (G : SimpleGraph V) :
    ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧
      ∀ {x y} (q : G.Walk x y), q.IsPath → q.length ≤ p.length := by
  classical
  let S : Finset ℕ := (Finset.range (Fintype.card V)).filter
    (fun n => ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ p.length = n)
  let a₀ : V := Classical.choice inferInstance
  have hp₀ : (Walk.nil : G.Walk a₀ a₀).IsPath := Walk.IsPath.nil
  have hS : S.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨?_, a₀, a₀, Walk.nil, hp₀, rfl⟩⟩
    exact Finset.mem_range.mpr hp₀.length_lt
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image S id hS
  obtain ⟨a,b,p,hp,rfl⟩ := (Finset.mem_filter.mp hn).2
  refine ⟨a,b,p,hp,?_⟩
  intro x y q hq
  exact hmax q.length (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hq.length_lt, x,y,q,hq,rfl⟩)

/-- In a graph with unique continuation past any incoming edge, an edge
from a simple path to an outside vertex attaches at an endpoint. -/
lemma external_neighbor_endpoint_of_unique
    (huniq : ∀ v z a b, G.Adj v z → G.Adj v a → G.Adj v b →
      a ≠ z → b ≠ z → a = b)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (x y : V) (hx : x ∈ p.support) (hy : y ∉ p.support) (hxy : G.Adj x y) :
    x = a ∨ x = b := by
  induction p generalizing x with
  | nil =>
    exact Or.inl (List.mem_singleton.mp hx)
  | @cons a c b hac tail ih =>
    obtain ⟨htail,hano⟩ := (Walk.cons_isPath_iff _ _).mp hp
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl rfl
    have hynot : y ∉ tail.support := fun h => hy (List.mem_cons_of_mem a h)
    rcases ih htail x hx hynot hxy with rfl | hxb
    · cases tail with
      | nil => exact Or.inr rfl
      | @cons _ d _ hcd rest =>
        have hdm : d ∈ (Walk.cons hcd rest).support :=
          List.mem_cons_of_mem _ rest.start_mem_support
        have hda : d ≠ a := fun h => hano (h ▸ hdm)
        have hya : y ≠ a := fun h => hy (h ▸ List.mem_cons_self _ _)
        have heq : d = y := huniq x a d y hac.symm hcd hxy hda hya
        exact False.elim (hy (List.mem_cons_of_mem a (heq ▸ hdm)))
    · exact Or.inr hxb

/-- Unique continuation forces a longest path to contain the connected graph. -/
theorem exists_hamiltonian_path_of_unique [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected)
    (huniq : ∀ v z a b, G.Adj v z → G.Adj v a → G.Adj v b →
      a ≠ z → b ≠ z → a = b) :
    ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ p.support.toFinset = Finset.univ := by
  classical
  haveI : Nonempty V := hG.nonempty
  obtain ⟨a,b,p,hp,hlong⟩ := exists_longest_path G
  have hclosed : ∀ x ∈ p.support, ∀ y, G.Adj x y → y ∈ p.support := by
    intro x hx y hxy
    by_contra hy
    rcases external_neighbor_endpoint_of_unique huniq p hp x y hx hy hxy with rfl | rfl
    · have hnew : (Walk.cons hxy.symm p).IsPath :=
        (Walk.cons_isPath_iff _ _).mpr ⟨hp,hy⟩
      have hh := hlong _ hnew
      simp only [Walk.length_cons] at hh
      exact (Nat.not_succ_le_self _) hh
    · have hyrev : y ∉ p.reverse.support := by simpa using hy
      have hnew : (Walk.cons hxy.symm p.reverse).IsPath :=
        (Walk.cons_isPath_iff _ _).mpr ⟨hp.reverse,hyrev⟩
      have hh := hlong _ hnew
      simp only [Walk.length_cons,Walk.length_reverse] at hh
      exact (Nat.not_succ_le_self _) hh
  have hwalk : ∀ {u v} (_q : G.Walk u v), u ∈ p.support → v ∈ p.support := by
    intro u v q
    induction q with
    | nil => exact id
    | cons huv _tail ih =>
      intro hu
      exact ih (hclosed _ hu _ huv)
  refine ⟨a,b,p,hp,?_⟩
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨q⟩ := hG a x
  exact List.mem_toFinset.mpr (hwalk q p.start_mem_support)

/-- Every finite connected graph of maximum degree two has a Hamiltonian
simple path. Singletons and cycles are included. -/
theorem exists_hamiltonian_path [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (hdegree : ∀ v, G.degree v ≤ 2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ p.support.toFinset = Finset.univ := by
  apply exists_hamiltonian_path_of_unique G hG
  intro v z a b hz ha hb haz hbz
  exact neighbor_eq_of_degree_le_two G (hdegree v) hz ha hb haz hbz

#print axioms exists_longest_path
#print axioms external_neighbor_endpoint_of_unique
#print axioms exists_hamiltonian_path_of_unique
#print axioms exists_hamiltonian_path
end MaxCaterpillar.ExponentialPush.DegreeTwo
