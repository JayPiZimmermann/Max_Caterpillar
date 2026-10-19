import MaxCaterpillar.Internal.Network
import MaxNN.Constructions.Paramid.Caterpillar.SpineBound
import Mathlib.Algebra.BigOperators.Intervals

/-! # The finite construction data

Implementation details of the dictionary and its compilation are separate
from the elementary network and width definitions in `Definitions.lean`.
-/

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar Corrections

-- The dictionary inner product integrates against Haar measure on `Point N`.
attribute [local instance] Canonical.functionMeasureSpace Canonical.functionIsAddHaarMeasure

theorem Internal.maximum_eq_MAX (N : ℕ) [NeZero N] : Maximum N = MAX N := rfl

/-- The paper's sum over spine sizes `m = s + 2` is the internal closed count. -/
theorem Internal.coneCount_eq_spineConeBound (N : ℕ) :
    coneCount N = spineConeBound N := by
  cases N with
  | zero => rfl
  | succ n =>
    unfold coneCount spineConeBound
    rw [Nat.succ_sub_one, ← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun s _ => by rw [add_comm 2 s]; rfl

theorem Internal.secondWidth_eq (N : ℕ) :
    secondWidth N = spineConeBound N * 3 ^ (N - 2) - N * (N - 1) + 2 := by
  rw [secondWidth, Internal.coneCount_eq_spineConeBound]

noncomputable def activeSecondWidth (r : ℕ) : ℕ :=
  (essentialKeys (Canonical.canonicalActiveKeys r)).card + 2

/-- The public record of the compact dictionary network with second-layer keys
`K`, key coefficients `c`, and pair-feature remainder `q`. -/
noncomputable def ofCompact {n : ℕ} (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (Width.W (n + 1)) → ℝ) : Network (n + 1) (compactWidth n) (K.card + 2) :=
  Internal.ofLayers (compactFeatureLayer n)
    (compactDictionarySecondLayer K (compactOfPairCoeff q)) (dictionaryOutput K c)

theorem ofCompact_eval {n : ℕ} (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (Width.W (n + 1)) → ℝ) (x : Point (n + 1)) :
    (ofCompact K c q).eval x = (compactOfDictionaryNetwork K c q).eval x 0 :=
  Internal.ofLayers_eval _ _ _ x

/-- The direct caterpillar dictionary, normalized and pruned, with single
hinges absorbed into the shared feature layer. The data is nonrecursive. -/
noncomputable def network (r : ℕ) :
    Network (r + 1 + 1) (2 + (r + 1 + (r + 1 + 1).choose 2)) (activeSecondWidth r) :=
  ofCompact (essentialKeys (Canonical.canonicalActiveKeys r)) (Canonical.canonicalNormalizedCoeff r)
    (absorbedRemainderCoeff (Canonical.canonicalActiveKeys r)
      (Canonical.canonicalNormalizedCoeff r) (Canonical.canonicalRemainderCoeff r))

theorem network_eval_internal (r : ℕ) (x : Point (r + 1 + 1)) :
    (network r).eval x = (compactEssentialNetwork r).eval x 0 :=
  ofCompact_eval _ _ _ x

/-- Raw face keys and shared features, before merging equal functions. -/
abbrev Atom (r : ℕ) := Corrections.Canonical.AtomIndex r

noncomputable abbrev atom (r : ℕ) : Atom r → Point (r + 1 + 1) → ℝ :=
  Corrections.Canonical.atomFunction r

/-- The finite set of distinct functions represented by the raw tags. -/
noncomputable abbrev dictionary (r : ℕ) : Finset (Point (r + 1 + 1) → ℝ) :=
  Corrections.Canonical.taggedDictionary (atom r)

/-- Average inverse-Gram coefficient, divided among duplicate tags. -/
noncomputable abbrev coefficient (r : ℕ) : Atom r → ℝ :=
  Corrections.Canonical.taggedCoeff (atom r) (Maximum (r + 1 + 1))

end MaxCaterpillar
