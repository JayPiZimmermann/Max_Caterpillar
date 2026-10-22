import MaxCaterpillar.CountLower.Combinatorics
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Normalize

/-! # Normalized caterpillar face functions in full coordinates

Every normalized face key `k` of the caterpillar dictionary is a face function
`σ(∑ₒ hₒ yₒ + ∑_{(i,j) ∈ M} σ(y_i - y_j))` with an integer head `h`, pairs
`i < j`, `∑ h = 0`, an apex `π 0` with `h = -1` met by no pair, and at most
`N - 2` pairs.  The head in full coordinates is `fullCoord k.1`.
-/

open BigOperators

namespace MaxCaterpillar.CountLower

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections ParamidGeom ParamidChain

/-! ## Full coordinates -/

/-- The full-coordinate vector of a reduced vector `v`:
`⟨v, coordT y⟩ = ∑ₒ (fullCoord v)ₒ yₒ`. -/
noncomputable def fullCoord {n : ℕ} (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (-∑ i, v i) v

/-- `fullCoord` as a linear map. -/
noncomputable def fullLin (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun := fullCoord
  map_add' v w := by
    funext o
    refine Fin.cases ?_ (fun i => ?_) o
    · simp only [fullCoord, Fin.cons_zero, Pi.add_apply, Finset.sum_add_distrib]
      ring
    · simp only [fullCoord, Fin.cons_succ, Pi.add_apply]
  map_smul' c v := by
    funext o
    refine Fin.cases ?_ (fun i => ?_) o
    · simp only [fullCoord, Fin.cons_zero, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
        RingHom.id_apply]
      ring
    · simp only [fullCoord, Fin.cons_succ, Pi.smul_apply, RingHom.id_apply]

theorem fullCoord_add {n : ℕ} (v w : Fin n → ℝ) :
    fullCoord (v + w) = fullCoord v + fullCoord w := (fullLin n).map_add v w

theorem fullCoord_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    fullCoord (∑ i in s, f i) = ∑ i in s, fullCoord (f i) := map_sum (fullLin n) f s

theorem sum_fullCoord {n : ℕ} (v : Fin n → ℝ) : ∑ o, fullCoord v o = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [fullCoord, Fin.cons_zero, Fin.cons_succ]
  ring

theorem dot_coordT_eq {n : ℕ} (v : Fin n → ℝ) (y : Fin (n + 1) → ℝ) :
    dot v ((CoordAux.coordT n).mulVec y) = ∑ o, fullCoord v o * y o := by
  rw [MaxNN.Width.dot_coordT, Fin.sum_univ_succ]
  simp only [fullCoord, Fin.cons_zero, Fin.cons_succ, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  ring

theorem fullCoord_vtx {n : ℕ} (a : Fin (n + 1)) (o : Fin (n + 1)) :
    fullCoord (toR (vtx a)) o = χ a o - χ 0 o := by
  unfold χ
  refine Fin.cases ?_ (fun j => ?_) a
  · rw [vtx_zero, sub_self]
    have h0 : toR (0 : Γ n) = 0 := by
      funext i
      simp [toR]
    rw [h0]
    refine Fin.cases ?_ (fun i => ?_) o
    · simp [fullCoord]
    · simp [fullCoord]
  · rw [vtx_succ]
    have hs : ∑ i, toR (Pi.single j 1 : Γ n) i = 1 := by
      simp [toR, Pi.single_apply]
    refine Fin.cases ?_ (fun i => ?_) o
    · simp only [fullCoord, Fin.cons_zero, hs]
      simp [(Fin.succ_ne_zero j).symm]
    · simp only [fullCoord, Fin.cons_succ]
      simp [toR, Pi.single_apply, Fin.succ_inj, Fin.succ_ne_zero]

theorem fullCoord_vtx_sub {n : ℕ} (a b : Fin (n + 1)) (o : Fin (n + 1)) :
    fullCoord (toR (vtx a) - toR (vtx b)) o = χ a o - χ b o := by
  have h := congrFun ((fullLin n).map_sub (toR (vtx a)) (toR (vtx b))) o
  change fullCoord (toR (vtx a) - toR (vtx b)) o =
    fullCoord (toR (vtx a)) o - fullCoord (toR (vtx b)) o at h
  rw [h, fullCoord_vtx, fullCoord_vtx]
  ring

/-! ## From label data to a description -/

/-- A real number is an integer. -/
def IsInt (x : ℝ) : Prop := ∃ z : ℤ, x = z

theorem IsInt.add {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; ring⟩

theorem IsInt.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, IsInt (f i)) :
    IsInt (∑ i in s, f i) :=
  Finset.sum_induction f IsInt (fun _ _ => IsInt.add) ⟨0, by norm_num⟩ h

theorem isInt_chi_sub {N : ℕ} (a b o : Fin N) : IsInt (χ a o - χ b o) := by
  unfold χ
  split_ifs
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- Label data in full coordinates gives a description with the key facts. -/
theorem exists_descr_of_labels {n : ℕ} (k : RealKey n) (apex : Fin (n + 1))
    (hL : ∀ v ∈ k.2, ∃ p : Fin (n + 1) × Fin (n + 1), p.1 < p.2 ∧ p.1 ≠ apex ∧
      p.2 ≠ apex ∧ v = toR (vtx p.1) - toR (vtx p.2))
    (hint : ∀ o, IsInt (fullCoord k.1 o)) (hapex : fullCoord k.1 apex = -1)
    (hcard : k.2.card + 2 ≤ n + 1) :
    ∃ D : Descr (n + 1), Good D apex ∧ ∀ y, realUnitY k y = D.unit y := by
  classical
  choose h hh using hint
  choose! p hp using hL
  refine ⟨⟨h, k.2.image p⟩, ⟨?_, ?_, ?_, ?_⟩, fun y => ?_⟩
  · have : ((∑ o, h o : ℤ) : ℝ) = 0 := by
      push_cast
      rw [← sum_fullCoord k.1]
      exact Finset.sum_congr rfl fun o _ => (hh o).symm
    exact_mod_cast this
  · have : ((h apex : ℤ) : ℝ) = -1 := by rw [← hh, hapex]
    exact_mod_cast this
  · intro m hm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨(hp v hv).1, (hp v hv).2.1, (hp v hv).2.2.1⟩
  · exact le_trans (Nat.add_le_add_right Finset.card_image_le 2) hcard
  · unfold realUnitY paramidOn Descr.unit Descr.arg
    congr 1
    rw [dot_coordT_eq, Finset.sum_image]
    · congr 1
      · exact Finset.sum_congr rfl fun o _ => by rw [hh o]
      · refine Finset.sum_congr rfl fun v hv => ?_
        conv_lhs => rw [(hp v hv).2.2.2]
        rw [SupportCut.dot_sub_left, MaxNN.Width.dot_toR_vtx_coordT,
          MaxNN.Width.dot_toR_vtx_coordT]
        congr 1
        ring
    · intro v hv w hw he
      rw [(hp v hv).2.2.2, (hp w hw).2.2.2, he]

/-! ## The caterpillar labels -/

variable {r : ℕ}

theorem wordLabels_endpoints (w : WordIndex r) :
    ∀ z ∈ wordLabels w, ∃ x y : Fin (r + 1 + 1), x ≠ y ∧ x ≠ w.1 0 ∧ y ≠ w.1 0 ∧
      z = toR (vtx x) - toR (vtx y) := by
  intro z hz
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
  refine ⟨w.1 (parent w.2.1 j.succ).succ, w.1 j.succ.succ, ?_, ?_, ?_, rfl⟩
  · intro h
    have hh := Fin.succ_injective _ (w.1.injective h)
    exact (ne_of_lt (parent_lt (Fin.succ_pos j))) hh
  · intro h
    exact Fin.succ_ne_zero _ (w.1.injective h)
  · intro h
    exact Fin.succ_ne_zero _ (w.1.injective h)

theorem orientedLabel_vtx_sub {n : ℕ} {x y : Fin (n + 1)} (hxy : x ≠ y) :
    ∃ p : Fin (n + 1) × Fin (n + 1), p.1 < p.2 ∧
      ((p.1 = x ∧ p.2 = y) ∨ (p.1 = y ∧ p.2 = x)) ∧
      orientedLabel (toR (vtx x) - toR (vtx y)) = toR (vtx p.1) - toR (vtx p.2) := by
  unfold orientedLabel
  rcases lt_or_gt_of_ne hxy with h | h
  · refine ⟨(x, y), h, Or.inl ⟨rfl, rfl⟩, ?_⟩
    rw [if_neg]
    rintro ⟨a, b, hba, he⟩
    obtain ⟨rfl, rfl⟩ := simplex_difference_endpoints hxy he
    exact absurd h (not_lt.mpr hba.le)
  · refine ⟨(y, x), h, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [if_pos ⟨x, y, h, rfl⟩, neg_sub]

/-- **Key facts.** Every normalized face key is a face function with an integer
head summing to zero, pairs `i < j`, an apex of head `-1` met by no pair, and
at most `N - 2` pairs. -/
theorem exists_descr {k : RealKey (r + 1)} (hk : k ∈ normalizedKeys r) :
    ∃ (D : Descr (r + 1 + 1)) (apex : Fin (r + 1 + 1)),
      Good D apex ∧ ∀ y, realUnitY k y = D.unit y := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨k', hk', hqk⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hk'
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hqk
  have hlab := wordLabels_endpoints w
  set V := wordLabels w
  have hsub : (faceKey (wordKey w).1 (wordKey w).2 τ).2 ⊆ V := by
    unfold faceKey
    exact Finset.filter_subset _ _
  -- the labels of the normalized key
  have hL : ∀ v ∈ (normalizedKey (faceKey (wordKey w).1 (wordKey w).2 τ)).2,
      ∃ p : Fin (r + 1 + 1) × Fin (r + 1 + 1), p.1 < p.2 ∧ p.1 ≠ w.1 0 ∧
        p.2 ≠ w.1 0 ∧ v = toR (vtx p.1) - toR (vtx p.2) := by
    intro v hv
    unfold normalizedKey at hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨x, y, hxy, hx, hy, rfl⟩ := hlab z (hsub hz)
    obtain ⟨p, hp, hpe, he⟩ := orientedLabel_vtx_sub hxy
    refine ⟨p, hp, ?_, ?_, he⟩
    · rcases hpe with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> assumption
    · rcases hpe with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2] <;> assumption
  -- every label has integer full coordinates and vanishes at the apex
  have hz : ∀ z ∈ V, ∀ o, IsInt (fullCoord z o) ∧ fullCoord z (w.1 0) = 0 := by
    intro z hz o
    obtain ⟨x, y, -, hx, hy, rfl⟩ := hlab z hz
    refine ⟨by rw [fullCoord_vtx_sub]; exact isInt_chi_sub x y o, ?_⟩
    rw [fullCoord_vtx_sub]
    unfold χ
    rw [if_neg (Ne.symm hx), if_neg (Ne.symm hy), sub_self]
  have hγ : ∀ o, fullCoord (wordGamma w) o = χ (w.1 (lastHead w.2.1).succ) o - χ (w.1 0) o :=
    fun o => fullCoord_vtx_sub _ _ o
  -- the head in full coordinates
  have hhead : ∀ o, fullCoord (normalizedKey (faceKey (wordKey w).1 (wordKey w).2 τ)).1 o =
      fullCoord (wordGamma w) o +
        ∑ z in V.filter (fun v => keyExt V τ v = 1), fullCoord z o +
        ∑ z in (faceKey (wordKey w).1 (wordKey w).2 τ).2.filter reverseLabel,
          fullCoord z o := by
    intro o
    unfold normalizedKey
    rw [fullCoord_add, Pi.add_apply, fullCoord_sum, Finset.sum_apply]
    unfold faceKey
    rw [fullCoord_add, Pi.add_apply, fullCoord_sum, Finset.sum_apply]
    rfl
  have hint : ∀ o, IsInt
      (fullCoord (normalizedKey (faceKey (wordKey w).1 (wordKey w).2 τ)).1 o) := by
    intro o
    rw [hhead o, hγ o]
    refine IsInt.add (IsInt.add (isInt_chi_sub _ _ o) ?_) ?_
    · exact IsInt.sum _ _ fun z hz' => (hz z (Finset.mem_of_mem_filter z hz') o).1
    · exact IsInt.sum _ _ fun z hz' => (hz z (hsub (Finset.mem_of_mem_filter z hz')) o).1
  have hap : fullCoord (normalizedKey (faceKey (wordKey w).1 (wordKey w).2 τ)).1 (w.1 0) =
      -1 := by
    rw [hhead, hγ, Finset.sum_eq_zero fun z hz' => (hz z (Finset.mem_of_mem_filter z hz')
      (w.1 0)).2, Finset.sum_eq_zero fun z hz' =>
      (hz z (hsub (Finset.mem_of_mem_filter z hz')) (w.1 0)).2]
    unfold χ
    rw [if_neg (fun h => Fin.succ_ne_zero _ (w.1.injective h).symm), if_pos rfl]
    ring
  have hcard : (normalizedKey (faceKey (wordKey w).1 (wordKey w).2 τ)).2.card + 2 ≤
      r + 1 + 1 := by
    unfold normalizedKey
    have h2 := Finset.card_le_of_subset hsub
    have h3 : V.card = r := wordLabels_card w
    exact Nat.add_le_add_right (Finset.card_image_le.trans (h2.trans h3.le)) 2
  obtain ⟨D, hD⟩ := exists_descr_of_labels _ (w.1 0) hL hint hap hcard
  exact ⟨D, w.1 0, hD⟩

end MaxCaterpillar.CountLower
