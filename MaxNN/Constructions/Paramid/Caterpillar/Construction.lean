import MaxNN.Constructions.Paramid.Caterpillar.Formula.Correctness
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Canonical.Table
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Count

/-! # The explicit caterpillar network and its widths

For `N = r + 2`, the network data are defined by finite dictionaries and Gram
coefficients. There is no smaller-arity network call in this definition.
The widths below refer to the literal ordinary two-hidden-layer network.
-/

namespace MaxNN.Caterpillar

open ParamidGeom Corrections MaxNN.Width

/-- The first hidden layer contains coordinate signs and unordered pair hinges. -/
def firstWidth (r : ℕ) : ℕ := W (r + 1 + 1)

/-- Exactly the nonzero normalized correction coefficients, plus the two
neurons carrying the pair-linear remainder. -/
noncomputable def secondWidth (r : ℕ) : ℕ :=
  (Canonical.canonicalActiveKeys r).card + 2

/-- Network data depend on the input size alone. In particular, this
definition takes no class-identity or correctness proof as an argument. -/
noncomputable def network (r : ℕ) : ReLUNet (r + 1 + 1) 1 2 :=
  Canonical.canonicalNetworkCandidate r

theorem firstWidth_eq (r : ℕ) :
    firstWidth r = (r + 1 + 1).choose 2 + 2 * (r + 1 + 1) := W_eq _

theorem secondWidth_le_normalizedCones (r : ℕ) :
    secondWidth r ≤ (normalizedWordCones r).card * 3 ^ r + 2 := by
  exact Nat.add_le_add_right
    ((Canonical.canonicalActiveKeys_card_le_normalizedKeys r).trans
      card_normalizedKeys_le_normalizedWordCones) 2

theorem secondWidth_le_factorial (r : ℕ) :
    secondWidth r ≤ (r + 1 + 1).factorial * (2 ^ r - 1) * 3 ^ r + 2 := by
  exact (secondWidth_le_normalizedCones r).trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (3 ^ r) card_normalizedWordCones_le_factorial) 2)

/-- The literal network is already correct at the base arity `N = 3`. -/
theorem network_one_computes : (network 1).Computes (MAX 3) := by
  apply Canonical.canonicalNetworkCandidate_computes 1 (by decide)
  unfold FormulaClassIdentity
  rw [formula_one_eq_simplex, sub_self]
  exact Submodule.zero_mem _

/-- The directly defined two-hidden-layer network computes `MAX` at every
arity `r + 2 ≥ 3`, on all real inputs. -/
theorem network_computes (r : ℕ) (hr : 1 ≤ r) :
    (network r).Computes (MAX (r + 1 + 1)) :=
  Canonical.canonicalNetworkCandidate_computes r hr (formulaClassIdentity r hr)

/-- Exact hidden widths of the literal network defined above. -/
theorem twoLayerWidth (r : ℕ) (hr : 1 ≤ r) :
    TwoLayerWidth (r + 1 + 1) (firstWidth r) (secondWidth r)
      (MAX (r + 1 + 1)) := by
  refine ⟨featureLayer _, dictionarySecondLayer (Canonical.canonicalActiveKeys r)
      (Canonical.canonicalRemainderCoeff r),
    ReLUNet.affine (dictionaryOutput (Canonical.canonicalActiveKeys r)
      (Canonical.canonicalNormalizedCoeff r)), ?_⟩
  exact network_computes r hr

theorem twoLayerWidth_factorial (r : ℕ) (hr : 1 ≤ r) :
    TwoLayerWidth (r + 1 + 1) ((r + 1 + 1).choose 2 + 2 * (r + 1 + 1))
      ((r + 1 + 1).factorial * (2 ^ r - 1) * 3 ^ r + 2)
      (MAX (r + 1 + 1)) := by
  rw [← firstWidth_eq]
  exact (twoLayerWidth r hr).mono_right (secondWidth_le_factorial r)

end MaxNN.Caterpillar
