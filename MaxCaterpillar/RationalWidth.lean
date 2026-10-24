import MaxCaterpillar.Lemmas
import MaxCaterpillar.Compilation

/-! # Rational values and rational coefficient vectors

The dictionary functions, the auxiliary features, and the maximum are rational
at rational points, and the coefficient vectors of the compiled network are
rational; the projection argument of `Rationality.lean` then gives rational
expansions. The arities `N = 1, 2` are compiled directly
(`caterpillar_net_one`, `caterpillar_net_two`).
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width ParamidGeom ParamidChain

/-! ## Rational values at rational points -/

theorem relu_mem_ratField {t : ℝ} (ht : t ∈ ratField) : MaxNN.relu t ∈ ratField :=
  max_mem_ratField (Subfield.zero_mem _) ht

theorem dot_mem_ratField {m : ℕ} {v y : Fin m → ℝ} (hv : RatVec v) (hy : RatVec y) :
    dot v y ∈ ratField :=
  sum_mem_ratField _ fun i _ => Subfield.mul_mem _ (hv i) (hy i)

theorem ratVec_coordT {n : ℕ} {x : Fin (n + 1) → ℝ} (hx : x ∈ ratPoints (n + 1)) :
    RatVec ((CoordAux.coordT n).mulVec x) := by
  rw [CoordAux.coordT_mulVec]
  exact fun i => Subfield.sub_mem _ (hx _) (hx _)

theorem ratVec_toR {n : ℕ} (γ : Γ n) : RatVec (toR γ) := fun _ => intCast_mem_ratField _

theorem ratVec_of_simplexDifference {n : ℕ} {v : Fin n → ℝ} (hv : IsSimplexDifference v) :
    RatVec v := by
  obtain ⟨a, b, rfl⟩ := hv
  exact (ratVec_toR _).sub (ratVec_toR _)

theorem realUnitY_mem_ratField {n : ℕ} {k : RealKey n} (hγ : RatVec k.1)
    (hV : ∀ v ∈ k.2, IsSimplexDifference v) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ ratPoints (n + 1)) : realUnitY k x ∈ ratField := by
  rw [realUnitY_eq_relu]
  unfold realUnitArg
  exact relu_mem_ratField (Subfield.add_mem _ (dot_mem_ratField hγ (ratVec_coordT hx))
    (sum_mem_ratField _ fun v hv => relu_mem_ratField
      (dot_mem_ratField (ratVec_of_simplexDifference (hV v hv)) (ratVec_coordT hx))))

theorem feat_mem_ratField {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ ratPoints N) (j : Fin (W N)) :
    feat N x j ∈ ratField := by
  refine Fin.addCases (motive := fun j : Fin (N + (N + N.choose 2)) => feat N x j ∈ ratField)
    (fun i => ?_) (fun j => ?_) j
  · have h := feat_pos x i
    unfold posIdx at h
    dsimp only
    rw [h]
    exact relu_mem_ratField (hx i)
  · refine Fin.addCases (motive := fun j : Fin (N + N.choose 2) =>
      feat N x (Fin.natAdd N j) ∈ ratField) (fun i => ?_) (fun q => ?_) j
    · have h := feat_neg x i
      unfold negIdx at h
      dsimp only
      rw [h]
      exact relu_mem_ratField (Subfield.neg_mem _ (hx i))
    · have h := feat_pr x q
      unfold prIdx at h
      dsimp only
      rw [h]
      exact relu_mem_ratField (Subfield.sub_mem _ (hx _) (hx _))

theorem MAX_mem_ratField {N : ℕ} [NeZero N] {x : Fin N → ℝ} (hx : x ∈ ratPoints N) :
    MAX N x ∈ ratField := by
  obtain ⟨i, hi⟩ := exists_MAX_eq N x
  rw [hi]
  exact hx i

/-! ## Integer heads -/

variable {r : ℕ}

theorem ratVec_wordGamma (w : WordIndex r) : RatVec (wordGamma w) :=
  (ratVec_toR _).sub (ratVec_toR _)

theorem ratVec_correctionKey {k : RealKey (r + 1)} (hk : k ∈ correctionKeys r) :
    RatVec k.1 := by
  obtain ⟨k0, hk0, hkk⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hk0
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hkk
  exact (ratVec_wordGamma w).add (ratVec_sum _ fun v hv => ratVec_of_simplexDifference
    (wordLabels_simplexDifference w v (Finset.mem_of_mem_filter v hv)))

theorem ratVec_normalizedKey {k : RealKey (r + 1)} (hk : k ∈ normalizedKeys r) :
    RatVec k.1 := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
  unfold normalizedKey
  exact (ratVec_correctionKey hq).add (ratVec_sum _ fun v hv => ratVec_of_simplexDifference
    (correctionKeys_simplexDifference q hq v (Finset.mem_of_mem_filter v hv)))

theorem dictionary_eq_range : (↑(dictionary r) : Set (Point (r + 1 + 1) → ℝ)) =
    Set.range (atom r) := by
  letI : DecidableEq (Point (r + 1 + 1) → ℝ) := Classical.decEq _
  ext g
  rw [Finset.mem_coe]
  constructor
  · intro hg
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hg
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-! ## Rational coefficient vectors -/

theorem ratVec_unitCoef {n : ℕ} (u : Fin (W n)) : RatVec (unitCoef u) := ratVec_delta u

theorem ratVec_coordCoef {n : ℕ} (i : Fin n) : RatVec (coordCoef i) :=
  fun k => Subfield.sub_mem _ (ratVec_delta _ k) (ratVec_delta _ k)

theorem ratVec_pairMaxCoeff {n : ℕ} (a b : Fin n) : RatVec (pairMaxCoeff a b) := by
  classical
  unfold pairMaxCoeff
  split_ifs
  · exact (ratVec_coordCoef _).add (ratVec_unitCoef _)
  · exact (ratVec_coordCoef _).add (ratVec_unitCoef _)
  · exact ratVec_coordCoef _

theorem ratVec_hingeCoeff {n : ℕ} (a b : Fin n) : RatVec (hingeCoeff a b) :=
  (ratVec_pairMaxCoeff a b).sub (ratVec_coordCoef b)

/-- Arity one: the auxiliary feature `x₀` alone. -/
theorem caterpillar_net_one :
    ∃ net : Network 1 (firstWidth 1) (secondWidth 1),
      (∀ x, net.eval x = Maximum 1 x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases := by
  apply compile_expansion_width (n := 0) ∅ 0 (coordCoef 0) (by simp) (by simp) (by simp)
    (ratVec_coordCoef 0)
  · intro x
    have h : auxiliary (coordCoef 0) x = x 0 := by
      unfold auxiliary
      rw [sum_coordCoef, coordLin_feat]
    rw [Finset.sum_empty, h]
    exact (MAX_one x).trans (zero_add _).symm
  · exact Nat.le_add_left _ _

/-- Arity two: `max(x₀, x₁)` from the auxiliary features. -/
theorem caterpillar_net_two :
    ∃ net : Network 2 (firstWidth 2) (secondWidth 2),
      (∀ x, net.eval x = Maximum 2 x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases := by
  apply compile_expansion_width (n := 1) ∅ 0 (pairMaxCoeff 0 1) (by simp) (by simp) (by simp)
    (ratVec_pairMaxCoeff 0 1)
  · intro x
    have h : auxiliary (pairMaxCoeff 0 1) x = max (x 0) (x 1) := by
      unfold auxiliary
      rw [sum_pairMaxCoeff, pairMaxLin_feat]
    rw [Finset.sum_empty, h]
    exact (MAX_two x).trans (zero_add _).symm
  · exact Nat.le_add_left _ _

end MaxCaterpillar
