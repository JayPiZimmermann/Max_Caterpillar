import MaxCaterpillar.OneBasis

/-! # Rational weights by a ℚ-linear projection (Version 4)

Let `π : ℝ → ℚ` be a ℚ-linear map with `π q = q` on `ℚ` (a left inverse of the
inclusion `ℚ → ℝ`). If `f = ∑ dᵢ vᵢ` with real `dᵢ`, and `f` and every `vᵢ` are
rational at rational points, applying `π` to the identity at a rational point
`y` gives `f y = ∑ π(dᵢ) vᵢ y`. Both sides are continuous and agree on the dense
set `ℚ^N`, hence everywhere. No basis, independence, or row-span argument is
needed (compare `Rationality.lean`, Version 2/3), and the expansion keeps its
support, so it is applied directly to the essential normalized descriptions.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width

/-- Version 4 of `exists_rat_coeff_of_mem_span` (same statement): a function
in the span of a finite continuous family, all rational on rational points, has
rational coefficients in that family. Proof: apply a ℚ-linear projection
`ℝ → ℚ` to any real expansion at the rational points. -/
theorem exists_rat_coeff_of_mem_span_v4 {N : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → (Fin N → ℝ) → ℝ) (hc : ∀ i, Continuous (v i))
    (hv : ∀ i, ∀ y ∈ ratPoints N, v i y ∈ ratField)
    {f : (Fin N → ℝ) → ℝ} (hf : f ∈ Submodule.span ℝ (Set.range v))
    (hfr : ∀ y ∈ ratPoints N, f y ∈ ratField) :
    ∃ c : ι → ℝ, (∀ i, c i ∈ ratField) ∧ ∀ x, f x = ∑ i, c i * v i x := by
  obtain ⟨d, hd⟩ := (mem_span_range_iff_exists_fun ℝ).mp hf
  have hfx : ∀ x, f x = ∑ i, d i * v i x := fun x => by simp [← hd, Finset.sum_apply]
  obtain ⟨π, hπ⟩ := (Algebra.linearMap ℚ ℝ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℝ).injective)
  have hπq : ∀ q : ℚ, π q = q := fun q => by simpa using LinearMap.congr_fun hπ q
  refine ⟨fun i => (π (d i) : ℝ), fun i => ratCast_mem_ratField _, fun x => ?_⟩
  refine congrFun (eq_of_eq_on_ratPoints (f := f) (g := fun x => ∑ i, (π (d i) : ℝ) * v i x) ?_ ?_ fun y hy => ?_) x
  · simp only [funext hfx]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (hc i)
  · exact continuous_finset_sum _ fun i _ => continuous_const.mul (hc i)
  choose q hq using fun i => mem_ratField_iff.mp (hv i y hy)
  obtain ⟨p, hp⟩ := mem_ratField_iff.mp (hfr y hy)
  have h1 : ((p : ℚ) : ℝ) = ∑ i, q i • d i := by
    rw [hp, hfx]
    exact Finset.sum_congr rfl fun i _ => by rw [Rat.smul_def, hq, mul_comm]
  have h2 := congrArg π h1
  rw [hπq, map_sum] at h2
  simp only [map_smul, smul_eq_mul] at h2
  rw [← hp, h2]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by rw [hq, mul_comm]

/-- **Caterpillar Net (Version 4).** Same statement as `caterpillar_net`. For
`N ≥ 3`: `max_N` lies in the span of the essential normalized caterpillar
functions and the auxiliary functions; `exists_rat_coeff_of_mem_span_v4` makes
the coefficients rational, and the compilation theorem gives the network. -/
theorem caterpillar_net_v4 (N : ℕ) [NeZero N] :
    ∃ net : Network N (firstWidth N) (secondWidth N),
      (∀ x, net.eval x = Maximum N x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases := by
  classical
  rcases N with _ | _ | _ | r
  · exact absurd rfl (NeZero.ne 0)
  · exact maximum_width_rational_one
  · exact maximum_width_rational_two
  have hr : 1 ≤ r + 1 := Nat.le_add_left 1 r
  set K := essentialKeys (normalizedKeys (r + 1))
  have hKsub : K ⊆ normalizedKeys (r + 1) := essentialKeys_subset _
  let v : (↥K ⊕ Fin (W (r + 1 + 1 + 1))) → Point (r + 1 + 1 + 1) → ℝ :=
    Sum.elim (fun k => realUnitY k.1) fun j x => feat _ x j
  have hmax : MAX (r + 1 + 1 + 1) ∈ Submodule.span ℝ (Set.range v) := by
    rw [Set.Sum.elim_range, Submodule.span_union]
    exact vocabularySpan_le_essential (r + 1) (maximum_mem_dictionary (r + 1) hr)
  obtain ⟨c, hc, hcx⟩ := exists_rat_coeff_of_mem_span_v4 v
    (Sum.rec (fun k => (Canonical.realUnitY_posHomContinuous k.1
      (normalizedKeys_simplexDifference k.1 (hKsub k.2))).1)
      fun j => (Canonical.feat_posHomContinuous _ j).1)
    (Sum.rec (fun k _ hy => realUnitY_mem_ratField (ratVec_normalizedKey (hKsub k.2))
      (normalizedKeys_simplexDifference k.1 (hKsub k.2)) hy)
      fun j _ hy => feat_mem_ratField hy j)
    hmax fun y hy => MAX_mem_ratField hy
  let d : RealKey (r + 1 + 1) → ℝ := fun k => if h : k ∈ K then c (Sum.inl ⟨k, h⟩) else 0
  have hd : ∀ k (hk : k ∈ K), d k = c (Sum.inl ⟨k, hk⟩) := fun k hk => dif_pos hk
  have hle : K.card + 2 ≤ secondWidth (r + 1 + 1 + 1) := by
    have h5 := card_normalizedKeys_le_normalizedWordCones.trans
      (Nat.mul_le_mul_right (3 ^ (r + 1)) (normalized_cone_count (r + 1)))
    show K.card + 2 ≤ coneCount (r + 1 + 1 + 1) * 3 ^ (r + 1 + 1 + 1 - 2) -
      (r + 1 + 1 + 1) * (r + 1 + 1 + 1 - 1) + 2
    rw [show r + 1 + 1 + 1 - 2 = r + 1 by omega, show r + 1 + 1 + 1 - 1 = r + 1 + 1 by omega]
    exact Nat.add_le_add_right ((essentialNormalizedKeys_card_le_sub_orderedHinges hr).trans
      (Nat.sub_le_sub_right h5 _)) 2
  refine compile_expansion_width K d (fun j => c (Sum.inr j))
    (fun k hk => normalizedKeys_simplexDifference k (hKsub hk))
    (fun k hk => ratVec_normalizedKey (hKsub hk)) (fun k hk => (hd k hk).symm ▸ hc _)
    (fun j => hc _) (fun x => ?_) hle
  rw [hcx x, Fintype.sum_sum_type, ← Finset.sum_coe_sort K]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => by rw [hd k.1 k.2]; rfl) rfl

end MaxCaterpillar
