import MaxCaterpillar.Fiber.Count65.SectorQuotient.RootGraphs.Canonical

/-! # Input rigidity forced by the actual directed root graphs -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient
open MaxCaterpillar.Frontier

/-- An interior graph and an endpoint graph have different edge counts. -/
theorem interior_endpoint_not_isomorphic : ∀ q : Equiv.Perm (Fin 4),
    ¬ (∀ a b, Star.interiorEdge a b ↔ Star.endpointEdge (q a) (q b)) := by
  decide

/-- The same obstruction with its two graphs in the opposite order. -/
theorem endpoint_interior_not_isomorphic : ∀ q : Equiv.Perm (Fin 4),
    ¬ (∀ a b, Star.endpointEdge a b ↔ Star.interiorEdge (q a) (q b)) := by
  decide

/-- Positive row rescaling and row permutations cannot hide a nontrivial input
permutation between two canonical mixed first hidden layers. -/
theorem mixed_input_perm_trivial (t u : ℝ) (ht : 0 < t) (hu : 0 < u)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (h : ∀ j i, Mixed65.firstRows t j i = s j * Mixed65.firstRows u (p j) (q i)) :
    q = Equiv.refl _ := by
  apply Star.interior_stabilizer_trivial q
  intro a b
  rw [← mixed_directedRootGraph t ht a b,
    ← mixed_directedRootGraph u hu (q a) (q b)]
  exact directedRootGraph_relabel _ _ p q s hs h a b

/-- An actual positive scaling/permutation relation between star dictionaries
preserves endpoint status and forces the input permutation to be trivial. -/
theorem star_endpoint_status_and_input_perm (t u : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (h : ∀ j i, Star65.firstRows t j i = s j * Star65.firstRows u (p j) (q i)) :
    (t = 1 ↔ u = 1) ∧ q = Equiv.refl _ := by
  have hg (a b : Fin 4) :
      (if t = 1 then Star.endpointEdge a b else Star.interiorEdge a b) ↔
      (if u = 1 then Star.endpointEdge (q a) (q b) else Star.interiorEdge (q a) (q b)) := by
    rw [← star_directedRootGraph t ht ht1 a b,
      ← star_directedRootGraph u hu hu1 (q a) (q b)]
    exact directedRootGraph_relabel _ _ p q s hs h a b
  have hend : t = 1 ↔ u = 1 := by
    constructor
    · intro htend
      by_contra huend
      apply endpoint_interior_not_isomorphic q
      intro a b
      simpa only [htend,if_pos rfl,if_neg huend] using hg a b
    · intro huend
      by_contra htend
      apply interior_endpoint_not_isomorphic q
      intro a b
      simpa only [huend,if_pos rfl,if_neg htend] using hg a b
  refine ⟨hend,?_⟩
  by_cases htend : t = 1
  · have huend : u = 1 := hend.mp htend
    apply Star.endpoint_stabilizer_trivial q
    intro a b
    simpa only [if_pos htend,if_pos huend] using hg a b
  · have huend : u ≠ 1 := fun huend => htend (hend.mpr huend)
    apply Star.interior_stabilizer_trivial q
    intro a b
    simpa only [if_neg htend,if_neg huend] using hg a b

/-- Input rigidity without requesting the endpoint-status conclusion. -/
theorem star_input_perm_trivial (t u : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (h : ∀ j i, Star65.firstRows t j i = s j * Star65.firstRows u (p j) (q i)) :
    q = Equiv.refl _ :=
  (star_endpoint_status_and_input_perm t u ht ht1 hu hu1 p q s hs h).2

/-- A mixed/star scaling-permutation relation would have to preserve the
interior root graph and fix every input coordinate. -/
theorem mixed_star_input_perm_trivial (t u : ℝ)
    (ht : 0 < t) (hu : 0 < u) (hu1 : u ≤ 1)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (h : ∀ j i, Mixed65.firstRows t j i = s j * Star65.firstRows u (p j) (q i)) :
    u ≠ 1 ∧ q = Equiv.refl _ := by
  have hg (a b : Fin 4) : Star.interiorEdge a b ↔
      (if u = 1 then Star.endpointEdge (q a) (q b) else Star.interiorEdge (q a) (q b)) := by
    rw [← mixed_directedRootGraph t ht a b,
      ← star_directedRootGraph u hu hu1 (q a) (q b)]
    exact directedRootGraph_relabel _ _ p q s hs h a b
  have huend : u ≠ 1 := by
    intro huend
    apply interior_endpoint_not_isomorphic q
    intro a b
    simpa only [if_pos huend] using hg a b
  refine ⟨huend,?_⟩
  apply Star.interior_stabilizer_trivial q
  intro a b
  simpa only [if_neg huend] using hg a b

#check @directedRootGraph_relabel
#check @mixed_input_perm_trivial
#check @star_endpoint_status_and_input_perm
#print axioms directedRootGraph_relabel
#print axioms mixed_directedRootGraph
#print axioms star_directedRootGraph
#print axioms mixed_input_perm_trivial
#print axioms star_endpoint_status_and_input_perm
#print axioms mixed_star_input_perm_trivial
end MaxCaterpillar.Fiber.Count65.SectorQuotient
