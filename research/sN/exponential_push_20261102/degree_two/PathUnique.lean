import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Tactic

/-! In a graph of maximum degree two, a simple path is determined by its
length and its first directed edge. Endpoints are allowed to differ in the
statement: equality of the complete vertex lists is proved.
-/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.DegreeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Once a previous neighbor is excluded, there is at most one next
neighbor at a vertex of degree at most two. -/
lemma neighbor_eq_of_degree_le_two {u z a b : V} (hdegree : G.degree u≤2)
    (hz : G.Adj u z) (ha : G.Adj u a) (hb : G.Adj u b)
    (haz : a≠z) (hbz : b≠z) : a=b := by
  classical
  by_contra hab
  have hsub : ({z,a,b} : Finset V)⊆G.neighborFinset u := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact (G.mem_neighborFinset u _).mpr hz
    · exact (G.mem_neighborFinset u _).mpr ha
    · exact (G.mem_neighborFinset u _).mpr hb
  have hcard : ({z,a,b} : Finset V).card=3 := by
    simp [Ne.symm haz,Ne.symm hbz,hab]
  have hthree : 3≤G.degree u := by
    rw [←G.card_neighborFinset_eq_degree u,←hcard]
    exact Finset.card_le_of_subset hsub
  omega

/-- Equal-length simple paths continuing the same directed edge have the
same full support list. The two terminal vertices need not be identified
before applying the theorem. -/
theorem support_eq_after_same_edge (hdegree : ∀ u,G.degree u≤2)
    {u v : V} (p : G.Walk u v) :
    ∀ {z w : V} (h : G.Adj z u) (q : G.Walk u w),
      (SimpleGraph.Walk.cons h p).IsPath →
      (SimpleGraph.Walk.cons h q).IsPath →
      p.length=q.length → p.support=q.support := by
  induction p with
  | nil =>
    intro z w h q hp hq hlen
    cases q with
    | nil => rfl
    | cons hq q => simp only [SimpleGraph.Walk.length] at hlen
  | @cons u a v hua p ih =>
    intro z w h q hp hq hlen
    cases q with
    | nil => simp at hlen
    | @cons _ b _ hub q =>
      have haz : a≠z := by
        intro he
        have hz := ((SimpleGraph.Walk.cons_isPath_iff h _).mp hp).2
        apply hz
        rw [←he,SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ p.start_mem_support
      have hbz : b≠z := by
        intro he
        have hz := ((SimpleGraph.Walk.cons_isPath_iff h _).mp hq).2
        apply hz
        rw [←he,SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ q.start_mem_support
      have hab : a=b := neighbor_eq_of_degree_le_two G (hdegree u) h.symm hua hub haz hbz
      subst b
      simp only [SimpleGraph.Walk.support_cons,List.cons.injEq,true_and]
      exact ih hua q hp.of_cons hq.of_cons (Nat.succ.inj hlen)

/-- A simple path with a fixed start is determined, as a vertex list, by
its length and the vertex reached by its first step. This also includes
the zero-length boundary case. -/
theorem support_eq_of_first_step (hdegree : ∀ u,G.degree u≤2)
    {u v w : V} (p : G.Walk u v) (q : G.Walk u w)
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length=q.length)
    (hfirst : p.getVert 1=q.getVert 1) : p.support=q.support := by
  cases p with
  | nil =>
    cases q with
    | nil => rfl
    | cons hq q => simp only [SimpleGraph.Walk.length] at hlen
  | @cons _ a _ hua p =>
    cases q with
    | nil => simp at hlen
    | @cons _ b _ hub q =>
      have hab : a=b := by simpa [SimpleGraph.Walk.getVert] using hfirst
      subst b
      simp only [SimpleGraph.Walk.support_cons,List.cons.injEq,true_and]
      exact support_eq_after_same_edge G hdegree p hua q hp hq (Nat.succ.inj hlen)

#print axioms neighbor_eq_of_degree_le_two
#print axioms support_eq_after_same_edge
#print axioms support_eq_of_first_step

end MaxCaterpillar.ExponentialPush.DegreeTwo
