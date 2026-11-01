import MaxCaterpillar.Fiber.Symmetry
import MaxCaterpillar.Fiber.Mixed65.Construction

/-! # Separation in the actual symmetry quotient

A nonempty proper invariant clopen subset gives two different connected
components of the quotient. The topological hypotheses remain explicit: the
existence of two representatives alone does not establish disconnection.

The mixed sector below is defined directly from the first weight matrix of
actual exact networks, followed by the genuine symmetry saturation. Its
definition imposes no condition of openness, closedness, or connectivity.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open Set Function

universe u v

/-- A nonempty proper clopen set distinguishes two connected components.
No finiteness assumption on the set of components is made. -/
theorem nontrivial_connectedComponents_of_isClopen
    {X : Type u} [TopologicalSpace X] {S : Set X}
    (hclopen : IsClopen S) (hin : S.Nonempty) (hout : Sᶜ.Nonempty) :
    Nontrivial (ConnectedComponents X) := by
  obtain ⟨x, hx⟩ := hin
  obtain ⟨y, hy⟩ := hout
  refine ⟨⟨(x : ConnectedComponents X), (y : ConnectedComponents X), ?_⟩⟩
  intro hxy
  have hyc : y ∈ connectedComponent x := ConnectedComponents.coe_eq_coe'.mp hxy.symm
  exact hy (hclopen.connectedComponent_subset hx hyc)

/-- Distinct connected components refute preconnectedness of the whole space. -/
theorem not_preconnectedSpace_of_nontrivial_components
    {X : Type u} [TopologicalSpace X] (h : Nontrivial (ConnectedComponents X)) :
    ¬ PreconnectedSpace X := by
  intro hpre
  letI := hpre
  have hsub : Subsingleton (ConnectedComponents X) := by
    constructor
    intro c d
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
    apply ConnectedComponents.coe_eq_coe.mpr
    rw [PreconnectedSpace.connectedComponent_eq_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  exact (@not_nontrivial (ConnectedComponents X) hsub) h

/-- Saturation is precisely what makes an image recover the original set
under the quotient map. -/
theorem preimage_image_eq_of_saturated
    {X : Type u} {Y : Type v} (q : X → Y) (S : Set X)
    (hsat : ∀ x y, q x = q y → (x ∈ S ↔ y ∈ S)) :
    q ⁻¹' (q '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (hsat y x hyx).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The quotient image of an invariant clopen set is clopen for the genuine
quotient topology, including when the quotient is not Hausdorff. -/
theorem isClopen_image_of_saturated
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hq : QuotientMap q) {S : Set X}
    (hsat : ∀ x y, q x = q y → (x ∈ S ↔ y ∈ S)) (hclopen : IsClopen S) :
    IsClopen (q '' S) := by
  have heq := preimage_image_eq_of_saturated q S hsat
  constructor
  · apply hq.isOpen_preimage.mp
    rw [heq]
    exact hclopen.isOpen
  · apply hq.isClosed_preimage.mp
    rw [heq]
    exact hclopen.isClosed

/-- A proper invariant clopen set proves that a quotient has more than one
connected component, without asserting an exact finite count. -/
theorem nontrivial_quotient_connectedComponents_of_isClopen
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hq : QuotientMap q) {S : Set X}
    (hsat : ∀ x y, q x = q y → (x ∈ S ↔ y ∈ S)) (hclopen : IsClopen S)
    (hin : S.Nonempty) (hout : Sᶜ.Nonempty) :
    Nontrivial (ConnectedComponents Y) := by
  apply nontrivial_connectedComponents_of_isClopen
    (isClopen_image_of_saturated hq hsat hclopen) (hin.image q)
  obtain ⟨y, hy⟩ := hout
  refine ⟨q y, ?_⟩
  intro hqy
  exact hy ((preimage_image_eq_of_saturated q S hsat).subset hqy)

variable {N h₁ h₂ : ℕ} [NeZero N]

/-- Membership is unchanged under the allowed finite sequences of symmetries. -/
def SymmetryInvariant (S : Set (ExactFiber N h₁ h₂)) : Prop :=
  ∀ x y, EqvGen SymmetryStep x y → (x ∈ S ↔ y ∈ S)

/-- Saturation under positive hidden scaling and all stated permutations.
Only actual exact networks enter this set. -/
def symmetrySaturation (S : Set (ExactFiber N h₁ h₂)) : Set (ExactFiber N h₁ h₂) :=
  {x | ∃ a, a ∈ S ∧ EqvGen SymmetryStep a x}

theorem subset_symmetrySaturation (S : Set (ExactFiber N h₁ h₂)) :
    S ⊆ symmetrySaturation S := by
  intro x hx
  exact ⟨x, hx, EqvGen.refl x⟩

theorem symmetrySaturation_invariant (S : Set (ExactFiber N h₁ h₂)) :
    SymmetryInvariant (symmetrySaturation S) := by
  intro x y hxy
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, EqvGen.trans _ _ _ hax hxy⟩
  · rintro ⟨a, ha, hay⟩
    exact ⟨a, ha, EqvGen.trans _ _ _ hay (EqvGen.symm _ _ hxy)⟩

/-- A generator-by-generator invariance proof extends to the full setoid. -/
theorem symmetryInvariant_of_step (S : Set (ExactFiber N h₁ h₂))
    (hstep : ∀ x y, SymmetryStep x y → (x ∈ S ↔ y ∈ S)) : SymmetryInvariant S := by
  intro x y hxy
  induction hxy with
  | rel x y h => exact hstep x y h
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

theorem symmetrySaturation_eq_preimage_image (S : Set (ExactFiber N h₁ h₂)) :
    symmetrySaturation S = quotientMk ⁻¹' (quotientMk '' S) := by
  ext x
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, (quotientMk_eq_iff a x).mpr hax⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, (quotientMk_eq_iff a x).mp hax⟩

/-- The exact symmetry-quotient separation theorem. Clopenness is a substantive
proof obligation on the original full exact fiber. -/
theorem symmetryQuotient_nontrivial_components_of_isClopen
    {S : Set (ExactFiber N h₁ h₂)} (hinv : SymmetryInvariant S)
    (hclopen : IsClopen S) (hin : S.Nonempty) (hout : Sᶜ.Nonempty) :
    Nontrivial (ConnectedComponents (SymmetryQuotient N h₁ h₂)) :=
  nontrivial_quotient_connectedComponents_of_isClopen quotientMk_quotientMap
    (fun x y hxy => hinv x y ((quotientMk_eq_iff x y).mp hxy)) hclopen hin hout

/-- More than one component contradicts the exact one-component proposition. -/
theorem not_hasComponentCount_one_of_nontrivial
    (h : Nontrivial (ConnectedComponents (SymmetryQuotient N h₁ h₂))) :
    ¬ HasComponentCount N h₁ h₂ 1 := by
  rintro ⟨e⟩
  letI := h
  obtain ⟨c, d, hcd⟩ := exists_pair_ne (ConnectedComponents (SymmetryQuotient N h₁ h₂))
  exact hcd (e.injective (Subsingleton.elim _ _))

namespace Mixed65

/-- The normalized mixed first-hidden-layer family. All suffix weights and
all biases remain unrestricted, subject only to exactness of the network. -/
def seed : Set (ExactFiber 4 6 5) :=
  {net | ∃ t : ℝ, 0 < t ∧ net.val.W₁ = firstRows t}

/-- The mixed first-layer sector with every allowed symmetry restored. -/
def sector : Set (ExactFiber 4 6 5) := symmetrySaturation seed

theorem sector_invariant : SymmetryInvariant sector := symmetrySaturation_invariant seed

/-- Conditional topological assembly only. The concrete sector must still be
proved nonempty, proper, and clopen in the full exact fiber. -/
theorem quotient_nontrivial_components_of_sector_clopen
    (hclopen : IsClopen sector) (hin : sector.Nonempty) (hout : sectorᶜ.Nonempty) :
    Nontrivial (ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  symmetryQuotient_nontrivial_components_of_isClopen sector_invariant hclopen hin hout

end Mixed65

end MaxCaterpillar.Fiber
