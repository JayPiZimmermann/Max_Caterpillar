import MaxCaterpillar.Simplify.CoverageMain
open BigOperators
open MaxNN MaxCaterpillar

example : ∀ (r : ℕ) {K : Finset (Trees.TreeFace (r + 1 + 1))}, Trees.IsTreeExpansion r K → ∀ {s : ℕ}, (∀ F ∈ K, Simplify.OutLeafBound F.descr s) → ∀ {k : ℕ}, 3 ≤ k → k ≤ r + 1 + 1 → ((r + 1 + 1).choose k : ℝ) ≤ (16 * ((s : ℝ) + 1) / 3) ^ k * K.card :=
  @MaxCaterpillar.Simplify.tree_outLeaf_choose_le
#print axioms MaxCaterpillar.Simplify.tree_outLeaf_choose_le

example : ∀ (r : ℕ), 1 ≤ r → ∀ {K : Finset (Trees.TreeFace (r + 1 + 1))}, Trees.IsTreeExpansion r K → ∀ {s : ℕ}, (∀ F ∈ K, Simplify.OutLeafBound F.descr s) → (16 * ((s : ℝ) + 1) / 3 + 1) ^ (r + 1 + 1) ≤ ((r + 1 + 1 : ℕ) + 1) * (16 * ((s : ℝ) + 1) / 3) ^ (r + 1 + 1) * K.card :=
  @MaxCaterpillar.Simplify.tree_outLeaf_exponential
#print axioms MaxCaterpillar.Simplify.tree_outLeaf_exponential

example : ∀ (r : ℕ) {K₁ : Finset (FaceKey r)} {K₂ : Finset (Trees.TreeFace (r + 1 + 1))}, Trees.IsMixedExpansion r K₁ K₂ → ∀ {s : ℕ}, 1 ≤ s → (∀ F ∈ K₂, Simplify.OutLeafBound F.descr s) → ∀ {k : ℕ}, 3 ≤ k → k ≤ r + 1 + 1 → ((r + 1 + 1).choose k : ℝ) ≤ (16 * ((s : ℝ) + 1) / 3) ^ k * (K₁.card + K₂.card) :=
  @MaxCaterpillar.Simplify.mixed_outLeaf_choose_le
#print axioms MaxCaterpillar.Simplify.mixed_outLeaf_choose_le

example : ∀ (r : ℕ), 1 ≤ r → ∀ {K₁ : Finset (FaceKey r)} {K₂ : Finset (Trees.TreeFace (r + 1 + 1))}, Trees.IsMixedExpansion r K₁ K₂ → ∀ {s : ℕ}, 1 ≤ s → (∀ F ∈ K₂, Simplify.OutLeafBound F.descr s) → (16 * ((s : ℝ) + 1) / 3 + 1) ^ (r + 1 + 1) ≤ ((r + 1 + 1 : ℕ) + 1) * (16 * ((s : ℝ) + 1) / 3) ^ (r + 1 + 1) * ((K₁.card : ℝ) + K₂.card) :=
  @MaxCaterpillar.Simplify.mixed_outLeaf_exponential
#print axioms MaxCaterpillar.Simplify.mixed_outLeaf_exponential

example : ∀ {N : ℕ} {D : CountLower.Descr N}, (∀ m ∈ D.M, m.1 < m.2) → ∀ {Δ : ℕ}, Trees.HubOK D Δ → Simplify.OutLeafBound D Δ :=
  @MaxCaterpillar.Simplify.outLeafBound_of_hubOK
#print axioms MaxCaterpillar.Simplify.outLeafBound_of_hubOK

example : ∀ {N : ℕ} (F : Trees.TreeFace N) {Δ : ℕ}, (∀ u, F.hingeDeg u ≤ Δ) → Simplify.OutLeafBound F.descr Δ :=
  @MaxCaterpillar.Simplify.outLeafBound_of_hingeDeg_le
#print axioms MaxCaterpillar.Simplify.outLeafBound_of_hingeDeg_le

example : ∀ {N : ℕ} (a c : Fin N) (hac : c ≠ a), Simplify.OutLeafBound (Trees.starFace a c hac).descr 1 :=
  @MaxCaterpillar.Simplify.starFace_outLeafBound
#print axioms MaxCaterpillar.Simplify.starFace_outLeafBound
