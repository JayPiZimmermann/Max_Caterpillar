import MaxCaterpillar.Count.Passing

/-!
# Tree face descriptions as hinge forests

The description of a tree face `F` has ordered pairs (`descr_lt`), satisfies the leaf
property (`descr_leaf`), and every pair has a *child* endpoint, injectively
(`descr_child_spec`, `descr_child_inj`).  `starFace a c` is the rooted star of Brunck et al.
as a tree face.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

open MaxNN CountLower Count

namespace TreeFace

variable {N : ℕ} (F : TreeFace N)

theorem normPair_mem (p : Fin N × Fin N) (u : Fin N) :
    ((normPair p).1 = u ∨ (normPair p).2 = u) ↔ (p.1 = u ∨ p.2 = u) := by
  unfold normPair
  split_ifs <;> simp only <;> tauto

theorem gen_mem (v u : Fin N) :
    ((F.gen v).1 = u ∨ (F.gen v).2 = u) ↔ (v = u ∨ F.parent v = u) := by
  unfold gen
  split_ifs <;> simp only <;> tauto

theorem incid_descr_le (u : Fin N) : (incid F.descr.M u).card ≤ F.hingeDeg u := by
  classical
  unfold hingeDeg incid
  have hsub : F.descr.M.filter (fun m => m.1 = u ∨ m.2 = u) ⊆
      (F.edgeVerts.filter fun v => F.state v = .hinge ∧ (v = u ∨ F.parent v = u)).image
        fun v => normPair (F.gen v) := by
    intro m hm
    obtain ⟨hmM, hmu⟩ := mem_filter.mp hm
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hmM
    obtain ⟨hv1, hv2⟩ := mem_filter.mp hv
    refine mem_image.mpr ⟨v, mem_filter.mpr ⟨hv1, hv2, ?_⟩, rfl⟩
    exact (F.gen_mem v u).mp ((normPair_mem _ u).mp hmu)
  convert (card_le_of_subset hsub).trans card_image_le

theorem descr_lt : ∀ m ∈ F.descr.M, m.1 < m.2 := by
  intro m hm
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hm
  have hne := F.gen_ne (mem_filter.mp hv).1
  unfold normPair
  split_ifs with h
  · exact h
  · rcases lt_trichotomy (F.gen v).1 (F.gen v).2 with h' | h' | h'
    · exact absurd h' h
    · exact absurd h' hne
    · exact h'

theorem descr_leaf : LeafProp F.descr.M := by
  classical
  intro E hE hne
  set V := (F.edgeVerts.filter fun v => F.state v = .hinge).filter
    fun v => normPair (F.gen v) ∈ E
  have hVne : V.Nonempty := by
    obtain ⟨m, hm⟩ := hne
    obtain ⟨v, hv, rfl⟩ := mem_image.mp (hE hm)
    exact ⟨v, mem_filter.mpr ⟨hv, hm⟩⟩
  obtain ⟨v, hvV, hmax⟩ := exists_max_image V F.depth hVne
  obtain ⟨hv, hvE⟩ := mem_filter.mp hvV
  have hvEV := (mem_filter.mp hv).1
  refine ⟨normPair (F.gen v), hvE, v, ?_, ?_⟩
  · have := (normPair_mem (F.gen v) v).mpr ((F.gen_mem v v).mpr (Or.inl rfl))
    rcases this with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · intro m' hm' hm'u
    obtain ⟨v', hv', rfl⟩ := mem_image.mp (hE hm')
    have hv'V : v' ∈ V := mem_filter.mpr ⟨hv', hm'⟩
    have hv'E := (mem_filter.mp hv').1
    have hrel := (F.gen_mem v' v).mp ((normPair_mem _ v).mp hm'u)
    rcases hrel with h | h
    · rw [h]
    · exfalso
      have hv'm := (F.mem_edgeVerts).mp hv'E
      have hd := F.depth_lt v' hv'm.2 hv'm.1
      rw [h] at hd
      have := hmax v' hv'V
      omega

end TreeFace

/-! ## Tree faces -/

namespace TreeFace

variable {N : ℕ} (F : TreeFace N)

/-- The child endpoint of a tree edge. -/
noncomputable def child (m : Fin N × Fin N) : Fin N := by
  classical
  exact if m.1 ∈ F.edgeVerts ∧ F.parent m.1 = m.2 then m.1 else m.2

theorem normPair_gen_cases (v : Fin N) :
    normPair (F.gen v) = (v, F.parent v) ∨ normPair (F.gen v) = (F.parent v, v) := by
  unfold normPair gen
  split_ifs <;> simp

theorem child_normPair {v : Fin N} (hv : v ∈ F.edgeVerts) : F.child (normPair (F.gen v)) = v := by
  classical
  unfold child
  rcases F.normPair_gen_cases v with h | h <;> rw [h]
  · simp [hv]
  · rw [if_neg]
    rintro ⟨hp, hpp⟩
    have hv' := (F.mem_edgeVerts).mp hv
    have hp' := (F.mem_edgeVerts).mp hp
    have d1 := F.depth_lt v hv'.2 hv'.1
    have d2 := F.depth_lt (F.parent v) hp'.2 hp'.1
    rw [hpp] at d2
    omega

theorem descr_child_spec : ∀ m ∈ F.descr.M, F.child m = m.1 ∨ F.child m = m.2 := by
  intro m _
  unfold child
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem descr_child_inj : Set.InjOn F.child F.descr.M := by
  intro m hm m' hm' he
  obtain ⟨v, hv, rfl⟩ := mem_image.mp (mem_coe.mp hm)
  obtain ⟨v', hv', rfl⟩ := mem_image.mp (mem_coe.mp hm')
  rw [F.child_normPair (mem_filter.mp hv).1, F.child_normPair (mem_filter.mp hv').1] at he
  rw [he]

end TreeFace

/-! ## The rooted stars of Brunck et al. -/

/-- The rooted star with apex `a` and root `c` as a tree face: every other label is a leaf
of `c`, with the hinge `σ(y_c - y_l)`. -/
def starFace {N : ℕ} (a c : Fin N) (hac : c ≠ a) : TreeFace N where
  apex := a
  root := c
  parent := fun _ => c
  depth := fun v => if v = c then 0 else 1
  up := fun _ => true
  state := fun _ => .hinge
  root_ne_apex := hac
  parent_ne_apex := fun _ _ _ => hac
  depth_lt := fun v _ hvc => by simp [hvc]

end MaxCaterpillar.Trees
