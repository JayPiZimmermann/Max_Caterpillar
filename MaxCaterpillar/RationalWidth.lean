import MaxCaterpillar.Lemmas
import MaxCaterpillar.Compilation

/-! # Rational weights and zero biases (Version 2 of the main theorem)

The dictionary functions are rational at rational points, so the evaluation
argument of `Rationality.lean` applies to every basis of the dictionary.

* Version 1 coefficients (the inverse-Gram average) are rational: on each
  basis they are the unique coordinates of the maximum, which are rational.
  Hence the existing `network` has rational weights; its biases are zero.
* Version 2 coefficients: a rational expansion obtained from one basis of the
  dictionary, without any integral (`rational_expansion`).
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width ParamidGeom ParamidChain

attribute [local instance] Corrections.Canonical.functionMeasureSpace
  Corrections.Canonical.functionIsAddHaarMeasure

/-! ## Rational values at rational points -/

theorem natCast_mem_ratField (m : ℕ) : (m : ℝ) ∈ ratField := by
  have h := intCast_mem_ratField m
  rwa [Int.cast_ofNat] at h

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

theorem atom_continuous (i : Atom r) : Continuous (atom r i) :=
  (Corrections.Canonical.atomFunction_posHomContinuous r i).1

theorem atom_mem_ratField (i : Atom r) {x : Point (r + 1 + 1)}
    (hx : x ∈ ratPoints (r + 1 + 1)) : atom r i x ∈ ratField := by
  cases i with
  | inl k =>
      exact realUnitY_mem_ratField (ratVec_correctionKey k.2)
        (correctionKeys_simplexDifference k.1 k.2) hx
  | inr j => exact feat_mem_ratField hx j

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

/-! ## Version 1 coefficients are rational -/

/-- On every basis of the dictionary, the inverse-Gram coefficients are the
coordinates of the target; these are rational by the evaluation argument. -/
theorem canonicalCoeff_mem_ratField {N : ℕ} [Nontrivial (Fin N → ℝ)]
    (D : Finset ((Fin N → ℝ) → ℝ))
    (hD : ∀ g ∈ D, Corrections.Canonical.IsPosHomContinuous g)
    (hDr : ∀ g ∈ D, ∀ y ∈ ratPoints N, g y ∈ ratField)
    {f : (Fin N → ℝ) → ℝ} (hf : f ∈ Submodule.span ℝ (↑D : Set ((Fin N → ℝ) → ℝ)))
    (hfr : ∀ y ∈ ratPoints N, f y ∈ ratField) (g : (Fin N → ℝ) → ℝ) :
    Corrections.Canonical.canonicalCoeff D f g ∈ ratField := by
  classical
  unfold Corrections.Canonical.canonicalCoeff
  refine Subfield.mul_mem _ (Subfield.inv_mem _ (natCast_mem_ratField _))
    (sum_mem_ratField _ fun S hS => ?_)
  unfold Corrections.Canonical.basisCoeff
  split_ifs with hg
  · obtain ⟨hSD, hli, -⟩ := Corrections.Canonical.mem_basisSubsets_iff.mp hS
    have hexp := Corrections.Canonical.basisExpansion_eq hS hD hf
    apply coeff_mem_ratField_of_independent (fun h : ↑S => h.1)
    · exact fun h => (hD h.1 (hSD h.2)).1
    · exact hli
    · exact fun h y hy => hDr h.1 (hSD h.2) y hy
    · intro y hy
      have hy' := congrFun hexp y
      unfold Corrections.Canonical.basisExpansion Corrections.Canonical.lincomb at hy'
      rw [hy']
      exact hfr y hy
  · exact Subfield.zero_mem _

theorem coefficient_mem_ratField (hr : 1 ≤ r) (i : Atom r) : coefficient r i ∈ ratField := by
  classical
  unfold coefficient Corrections.Canonical.taggedCoeff
  refine Subfield.div_mem _ ?_ (natCast_mem_ratField _)
  apply canonicalCoeff_mem_ratField
  · intro g hg
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hg
    exact Corrections.Canonical.atomFunction_posHomContinuous r j
  · intro g hg y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hg
    exact atom_mem_ratField j hy
  · exact maximum_mem_dictionary r hr
  · intro y hy
    haveI : NeZero (r + 1 + 1) := ⟨by omega⟩
    exact MAX_mem_ratField hy

/-! ## Version 1 network: rational weights and zero biases -/

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

theorem ratVec_rootHingeCoeff {n : ℕ} (v : Fin n → ℝ) : RatVec (rootHingeCoeff v) := by
  classical
  unfold rootHingeCoeff
  refine ratVec_sum _ fun p _ => ?_
  split_ifs
  · exact ratVec_hingeCoeff _ _
  · exact ratVec_zero

theorem canonicalRawCoeff_mem_ratField (hr : 1 ≤ r) (k : RealKey (r + 1)) :
    Canonical.canonicalRawCoeff r k ∈ ratField := by
  unfold Canonical.canonicalRawCoeff
  split_ifs with hk
  · exact coefficient_mem_ratField hr (Sum.inl ⟨k, hk⟩)
  · exact Subfield.zero_mem _

theorem canonicalNormalizedCoeff_mem_ratField (hr : 1 ≤ r) (k : RealKey (r + 1)) :
    Canonical.canonicalNormalizedCoeff r k ∈ ratField :=
  sum_mem_ratField _ fun q _ => canonicalRawCoeff_mem_ratField hr q

theorem ratVec_canonicalRemainderCoeff (hr : 1 ≤ r) :
    RatVec (Canonical.canonicalRemainderCoeff r) :=
  fun i => coefficient_mem_ratField hr (Sum.inr i)

/-- Version 1 data (`network`, canonical inverse-Gram average): its weights are
rational and its biases vanish. -/
theorem network_hasRationalWeights (hr : 1 ≤ r) : (network r).HasRationalWeights := by
  apply ofCompact_hasRationalWeights
  · exact (ratVec_canonicalRemainderCoeff hr).add (ratVec_sum _ fun k _ =>
      RatVec.smul (canonicalNormalizedCoeff_mem_ratField hr k) (ratVec_rootHingeCoeff _))
  · intro k hk
    exact ratVec_normalizedKey (Finset.mem_filter.mp (essentialKeys_subset _ hk)).1
  · exact fun k _ => canonicalNormalizedCoeff_mem_ratField hr k

theorem network_hasZeroBiases : (network r).HasZeroBiases :=
  ofCompact_hasZeroBiases _ _ _

/-! ## Version 2 coefficients: one basis, no integral -/

/-- **Version 2 coefficient rule.** Selecting one basis of the dictionary and
taking the coordinates of the maximum gives rational coefficients. This is an
existence statement: the basis is not canonical. -/
theorem rational_expansion (hr : 1 ≤ r) :
    ∃ c : Atom r → ℝ, (∀ i, ∃ q : ℚ, (q : ℝ) = c i) ∧
      ∀ x, ∑ i, c i * atom r i x = Maximum (r + 1 + 1) x := by
  classical
  haveI : NeZero (r + 1 + 1) := ⟨by omega⟩
  have hspan := maximum_mem_dictionary r hr
  rw [dictionary_eq_range] at hspan
  obtain ⟨c, hc, hcx⟩ := exists_rat_coeff_of_mem_span (atom r) atom_continuous
    (fun i y hy => atom_mem_ratField i hy) hspan (fun y hy => MAX_mem_ratField hy)
  exact ⟨c, fun i => mem_ratField_iff.mp (hc i), fun x => (hcx x).symm⟩

/-! ## The strengthened width theorem -/

theorem network_eval (hr : 1 ≤ r) (x : Point (r + 1 + 1)) :
    (network r).eval x = Maximum (r + 1 + 1) x :=
  (network_eval_internal r x).trans (compactEssentialNetwork_computes r hr x)

theorem activeSecondWidth_le_secondWidth (hr : 1 ≤ r) :
    activeSecondWidth r ≤ secondWidth (r + 1 + 1) := by
  rw [Internal.secondWidth_eq,
    show r + 1 + 1 - 2 = r by omega, show r + 1 + 1 - 1 = r + 1 by omega]
  exact essentialSecondWidth_le_spine r hr

theorem maximum_width_rational_of_three_le (hr : 1 ≤ r) :
    ∃ net : Network (r + 1 + 1) (firstWidth (r + 1 + 1)) (secondWidth (r + 1 + 1)),
      (∀ x, net.eval x = Maximum (r + 1 + 1) x) ∧ net.HasRationalWeights ∧
        net.HasZeroBiases := by
  have hw := compactWidth_eq_firstWidth (r + 1)
  let net₀ : Network (r + 1 + 1) (firstWidth (r + 1 + 1)) (activeSecondWidth r) :=
    hw ▸ network r
  have heval : ∀ x, net₀.eval x = Maximum (r + 1 + 1) x := fun x => by
    rw [Network.cast_first_eval]; exact network_eval hr x
  obtain ⟨net, h, hrat, hzero⟩ := net₀.exists_widen (activeSecondWidth_le_secondWidth hr) heval
  exact ⟨net, h, hrat ((Network.cast_first_props hw _).1 (network_hasRationalWeights hr)),
    hzero ((Network.cast_first_props hw _).2 network_hasZeroBiases)⟩

theorem maximum_width_rational_one :
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

theorem maximum_width_rational_two :
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
