-- Exact public lower-bound types copied from baseline e1ebfc0d22ba9097ef0aa0fb322104cca80af660.
-- Generate only from the preserved baseline, never from the replacement proof.
import MaxCaterpillar
set_option autoImplicit false
set_option linter.unusedVariables false
open BigOperators
open MaxNN MaxCaterpillar MaxNN.Caterpillar

example : ∀ (r : ℕ) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Trees.IsMixedExpansion r K₁ K₂) {Δ : ℕ}
    (hΔ : 2 ≤ Δ) (hω : ∀ F ∈ K₂, Count.OmegaLe F.descr Δ) {m : ℕ} (hm : 3 ≤ m)
    (hmN : m ≤ r + 1 + 1),
    (r + 1 + 1).choose m ≤ (2 * Δ + 2) ^ m * (K₁.card + K₂.card) :=
  @MaxCaterpillar.unified_choose_le
#print axioms MaxCaterpillar.unified_choose_le

example : ∀ (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Trees.IsMixedExpansion r K₁ K₂) {Δ : ℕ}
    (hΔ : 2 ≤ Δ) (hω : ∀ F ∈ K₂, Count.OmegaLe F.descr Δ),
    (2 * Δ + 3) ^ (r + 1 + 1) ≤
      (r + 1 + 1 + 1) * (2 * Δ + 2) ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  @MaxCaterpillar.unified_exponential
#print axioms MaxCaterpillar.unified_exponential

example : ∀ (r : ℕ) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) {m : ℕ} (hm : 3 ≤ m) (hmN : m ≤ r + 1 + 1),
    (r + 1 + 1).choose m ≤ 6 ^ m * K.card :=
  @MaxCaterpillar.caterpillar_expansion_choose_le
#print axioms MaxCaterpillar.caterpillar_expansion_choose_le

example : ∀ (r : ℕ) (hr : 1 ≤ r) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K),
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * K.card :=
  @MaxCaterpillar.caterpillar_expansion_exponential
#print axioms MaxCaterpillar.caterpillar_expansion_exponential

example : ∀ (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Count.IsBrunckExpansion r K₁ K₂),
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  @MaxCaterpillar.brunck_expansion_exponential
#print axioms MaxCaterpillar.brunck_expansion_exponential

example : ∀ (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Trees.IsMixedExpansion r K₁ K₂) {Δ : ℕ}
    (hΔ : 2 ≤ Δ) (hdeg : ∀ F ∈ K₂, ∀ u, F.hingeDeg u ≤ Δ),
    (2 * Δ + 3) ^ (r + 1 + 1) ≤
      (r + 1 + 1 + 1) * (2 * Δ + 2) ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  @MaxCaterpillar.hingeDeg_expansion_exponential
#print axioms MaxCaterpillar.hingeDeg_expansion_exponential

example : ∀ (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (Trees.TreeFace (r + 1 + 1))} (hK : Trees.IsMixedExpansion r K₁ K₂) {s : ℕ}
    (hs : 1 ≤ s) (hout : ∀ F ∈ K₂, Count.OutLeafBound F.descr s),
    (2 * s + 5) ^ (r + 1 + 1) ≤
      (r + 1 + 1 + 1) * (2 * s + 4) ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  @MaxCaterpillar.outLeaf_expansion_exponential
#print axioms MaxCaterpillar.outLeaf_expansion_exponential

example : ∀ (r : ℕ) (hr : 1 ≤ r) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K),
    (r + 1 + 1) * (r + 1) ≤ 6 * K.card :=
  @MaxCaterpillar.caterpillar_expansion_quadratic
#print axioms MaxCaterpillar.caterpillar_expansion_quadratic

example : ∀ (r : ℕ) (hr : 1 ≤ r),
    r.factorial ≤ caterpillarDim r :=
  @MaxCaterpillar.caterpillarDim_ge
#print axioms MaxCaterpillar.caterpillarDim_ge

-- Newly registered finite-elimination lemma, exact type from verification/main.json.
example : ∀ {m : ℕ} (U : Submodule ℝ (Fin m → ℝ)) {𝔉 : Set (Finset (Fin m → ℝ))}, ParamidGeom.Faces.FaceClosed 𝔉 → ∀ {d : ℕ}, d < FiniteDimensional.finrank ℝ U → ∀ {g : (Fin m → ℝ) → ℝ}, g ∈ ParamidGeom.Faces.FSpan 𝔉 → g ∈ ParamidGeom.LSpan m d → g ∈ ParamidGeom.Faces.GSpanRel 𝔉 U :=
  @MaxNN.ParamidGeom.Faces.mem_GSpanRel_of_lt_finrank
#print axioms MaxNN.ParamidGeom.Faces.mem_GSpanRel_of_lt_finrank

open MaxNN.ParamidGeom

example : ∀ (r : ℕ) (hr : 1 ≤ r),
  Maximum (r + 1 + 1) ∈ Submodule.span ℝ
      (↑(dictionary r) : Set (Point (r + 1 + 1) → ℝ)) :=
  @MaxCaterpillar.maximum_mem_dictionary
#print axioms MaxCaterpillar.maximum_mem_dictionary

example : ∀ (r : ℕ) (hr : 1 ≤ r),
  formula r - hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) r :=
  @MaxCaterpillar.class_identity
#print axioms MaxCaterpillar.class_identity
