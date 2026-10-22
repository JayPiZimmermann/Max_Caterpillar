import MaxNN.CPWL.Def
import Mathlib.Topology.MetricSpace.Baire

/-!
# The Baire brick: full-dimensional pieces reach every point

`exists_mem_interior_nonempty_of_covers`: in a finite cover of `ℝ^d` by closed
polyhedra, every point lies in some piece with **nonempty interior**.  (Pieces with
empty interior are individually nowhere dense; by the Baire category theorem the
interiors of the pieces are jointly dense, and a finite union of closed sets contains
the closure of that dense union.)

This is the topological half of the "convex CPWL = max of its full-dimensional pieces"
theorem (`MaxNN/CPWL/Representation/ConvexMax.lean`).

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

/-- **Baire brick.**  Every point of a finite closed polyhedral cover of `ℝ^d` lies in
a piece with nonempty interior. -/
theorem exists_mem_interior_nonempty_of_covers {d n : ℕ} (P : Fin n → Polyhedron d)
    (covers : ∀ x : Fin d → ℝ, ∃ i, x ∈ (P i).carrier) (x : Fin d → ℝ) :
    ∃ i, x ∈ (P i).carrier ∧ (interior (P i).carrier).Nonempty := by
  have hU : (⋃ i, (P i).carrier) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨i, hi⟩ := covers y
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hdense : Dense (⋃ i, interior (P i).carrier) :=
    dense_iUnion_interior_of_closed (fun i => (P i).isClosed_carrier) hU
  have hx : x ∈ closure (⋃ i, interior (P i).carrier) := hdense x
  rw [closure_iUnion_of_finite] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hne : (interior (P i).carrier).Nonempty := by
    rcases Set.eq_empty_or_nonempty (interior (P i).carrier) with he | hne
    · rw [he, closure_empty] at hi
      exact absurd hi (Set.not_mem_empty x)
    · exact hne
  refine ⟨i, ?_, hne⟩
  have hsub : closure (interior (P i).carrier) ⊆ (P i).carrier := by
    have h1 : closure (interior (P i).carrier) ⊆ closure (P i).carrier :=
      closure_mono interior_subset
    rw [(P i).isClosed_carrier.closure_eq] at h1
    exact h1
  exact hsub hi

end MaxNN
