import MaxCaterpillar.Count.Main

/- Exact statements copied from baseline commit e1ebfc0d22ba9097ef0aa0fb322104cca80af660.
Only proof bodies are replaced by the current declarations. -/

open BigOperators Finset
open scoped Nat
namespace MaxCaterpillar
open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.Width
  CountLower Trees Count Audit

example (r : ℕ)
    (K : Finset (Caterpillar.Corrections.RealKey (r + 1)))
    (hK : K ⊆ Caterpillar.Corrections.normalizedKeys r)
    (d : Caterpillar.Corrections.RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x =
      ∑ k in K, d k * Caterpillar.Corrections.realUnitY k x + auxiliary a x) :
    (r + 1 + 1).choose 3 ≤ K.card * r :=
  caterpillar_choose_three_le r K hK d a h

#print axioms MaxCaterpillar.caterpillar_choose_three_le

example (r : ℕ) (hr : 1 ≤ r)
    (K : Finset (Caterpillar.Corrections.RealKey (r + 1)))
    (hK : K ⊆ Caterpillar.Corrections.normalizedKeys r)
    (d : Caterpillar.Corrections.RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x =
      ∑ k in K, d k * Caterpillar.Corrections.realUnitY k x + auxiliary a x) :
    (r + 1 + 1) * (r + 1) ≤ 6 * K.card :=
  caterpillar_count_lower r hr K hK d a h

#print axioms MaxCaterpillar.caterpillar_count_lower

example (r : ℕ) {ι : Type*} (K : Finset ι)
    (U : ι → (Fin (r + 1 + 1) → ℝ) → ℝ)
    (hU : ∀ i ∈ K, ∃ (D : Descr (r + 1 + 1)) (apex : Fin (r + 1 + 1)),
      Good D apex ∧ ∀ y, U i y = D.unit y)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * U k x + auxiliary a x) :
    (r + 1 + 1).choose 3 ≤ K.card * r :=
  Trees.choose_three_le_of_good r K U hU d a h

#print axioms MaxCaterpillar.Trees.choose_three_le_of_good

example (r : ℕ) (hr : 1 ≤ r) {ι : Type*} (K : Finset ι)
    (U : ι → (Fin (r + 1 + 1) → ℝ) → ℝ)
    (hU : ∀ i ∈ K, ∃ (D : Descr (r + 1 + 1)) (apex : Fin (r + 1 + 1)),
      Good D apex ∧ ∀ y, U i y = D.unit y)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * U k x + auxiliary a x) :
    (r + 1 + 1) * (r + 1) ≤ 6 * K.card :=
  Trees.count_lower_of_good r hr K U hU d a h

#print axioms MaxCaterpillar.Trees.count_lower_of_good

example {Δ s : ℕ} (hΔ : 2 ≤ Δ) (hs1 : 1 ≤ s) (hsΔ : s ≤ Δ) :
    (1 / 2 + 1 / (2 * Δ + 2 : ℝ)) * (1 + 1 / (2 * Δ + 2 : ℝ)) ^ s +
      (1 / (2 * Δ + 2 : ℝ)) ^ s / 2 ≤ 1 :=
  Count.star_weight_le_one hΔ hs1 hsΔ

#print axioms MaxCaterpillar.Count.star_weight_le_one

example {r : ℕ} {K₁ : Finset (FaceKey r)} {K₂ : Finset (TreeFace (r + 1 + 1))}
    (hK : IsMixedExpansion r K₁ K₂) {Δ : ℕ} (hΔ : 2 ≤ Δ) (hω : ∀ F ∈ K₂, OmegaLe F.descr Δ)
    {m : ℕ} (hm : 3 ≤ m) (hmN : m ≤ r + 1 + 1) :
    (r + 1 + 1).choose m ≤ (2 * Δ + 2) ^ m * (K₁.card + K₂.card) :=
  Count.unified_choose_le hK hΔ hω hm hmN

#print axioms MaxCaterpillar.Count.unified_choose_le

end MaxCaterpillar
