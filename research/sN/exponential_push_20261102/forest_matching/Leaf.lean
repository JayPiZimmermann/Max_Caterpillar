import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic

/-! Research-only finite forest leaf theorem, using a longest simple path. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.Forest
open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Deleting edges preserves acyclicity. -/
theorem acyclic_mono {H : SimpleGraph V} (hHG : H ≤ G) (hG : G.IsAcyclic) :
    H.IsAcyclic := by
  intro v p hp
  exact hG (p.mapLe hHG) (hp.mapLe hHG)

/-- Every nonempty finite forest has a vertex with exactly one neighbour. -/
theorem exists_leaf (hG : G.IsAcyclic) (hedge : ∃ a b, G.Adj a b) :
    ∃ v w, G.Adj v w ∧ ∀ u, G.Adj v u → u = w := by
  classical
  let S : Finset ℕ := (Finset.range (Fintype.card V)).filter
    (fun n => ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ p.length = n)
  obtain ⟨a₀,b₀,hab₀⟩ := hedge
  have hp₀ : (Walk.cons hab₀ Walk.nil).IsPath := by
    simp [Walk.cons_isPath_iff, hab₀.ne]
  have hS : S.Nonempty := by
    refine ⟨1, Finset.mem_filter.mpr ⟨?_, a₀, b₀, Walk.cons hab₀ Walk.nil, hp₀, rfl⟩⟩
    exact Finset.mem_range.mpr hp₀.length_lt
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image S id hS
  obtain ⟨a,b,p,hp,rfl⟩ := (Finset.mem_filter.mp hn).2
  have hlong : ∀ {x y} (q : G.Walk x y), q.IsPath → q.length ≤ p.length := by
    intro x y q hq
    exact hmax q.length (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hq.length_lt, x,y,q,hq,rfl⟩)
  have hpos : 0 < p.length := by
    have h := hlong (Walk.cons hab₀ Walk.nil) hp₀
    simp only [Walk.length_cons, Walk.length_nil] at h
    exact lt_of_lt_of_le (by decide : 0 < 1) h
  cases p with
  | nil => simp at hpos
  | cons hab tail =>
    refine ⟨a,_,hab,?_⟩
    intro u hau
    have hu : u ∈ (Walk.cons hab tail).support := by
      by_contra hu
      have hpath : (Walk.cons hau.symm (Walk.cons hab tail)).IsPath :=
        (Walk.cons_isPath_iff _ _).mpr ⟨hp,hu⟩
      have hh := hlong _ hpath
      simp only [Walk.length_cons] at hh
      omega
    have heq := hG.path_unique
      (⟨(Walk.cons hab tail).takeUntil u hu, hp.takeUntil hu⟩ : G.Path a u)
      (Path.singleton hau)
    have heq' := congrArg (fun q : G.Path a u => q.val.support) heq
    have hu' : u ∈ tail.support := by
      simpa only [Walk.support_cons, List.mem_cons, hau.ne.symm, false_or] using hu
    have heq'' : (tail.takeUntil u hu').support = [u] := by
      simpa only [Walk.takeUntil, dif_neg hau.ne, Path.singleton, Walk.support_cons,
        Walk.support_nil, List.cons.injEq, true_and] using heq'
    have hb := (tail.takeUntil u hu').start_mem_support
    rw [heq''] at hb
    exact (List.mem_singleton.mp hb).symm

#print axioms acyclic_mono
#print axioms exists_leaf
end MaxCaterpillar.ExponentialPush.Forest
