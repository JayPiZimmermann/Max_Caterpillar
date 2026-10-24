import MaxCaterpillar.Competing.Relation

/-! # Support functions of the pyramids of Brunck et al., Sec. 7.1

`paramidSupport_eq`: `h_{pyr_{e_v}(B_{v,π,M})}(y) =
y_v + σ(y_{π_q} - y_v + ∑_{i=2}^{N-1} σ(y_{π_{r(i)}} - y_{π_i}))`, and its identification
with the caterpillar functions and the rooted stars.
-/

open BigOperators

namespace MaxCaterpillar.BHRSY

open MaxNN.Caterpillar MaxNN.Caterpillar.Corrections

variable {r : ℕ} {v : Fin (r + 1 + 1)} (π : Ordering (r + 1 + 1) v)

/-- The linear form `p ↦ ⟨p, y⟩`. -/
noncomputable def evalL {n : ℕ} (y : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun p := ∑ k, p k * y k
  map_add' p q := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem evalL_apply {n : ℕ} (y p : Fin n → ℝ) : evalL y p = ∑ k, p k * y k := rfl

theorem evalL_single {n : ℕ} (y : Fin n → ℝ) (k : Fin n) : evalL y (Pi.single k 1) = y k := by
  rw [evalL_apply, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem evalL_zvec (M : Finset ℕ) (t : ℕ → ℝ) (y : Fin (r + 1 + 1) → ℝ) :
    evalL y (zvec π M t) = y (π.pos (lastMarked M)) +
      ∑ i in Finset.Icc 2 (r + 1), t i * (y (π.pos (markedParent M i)) - y (π.pos i)) := by
  unfold zvec
  rw [map_add, map_sum, evalL_single]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_sub, evalL_single, evalL_single, smul_eq_mul]

theorem mul_le_relu {t b : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t * b ≤ MaxCaterpillar.relu b := by
  rcases le_total 0 b with hb | hb
  · calc t * b ≤ 1 * b := mul_le_mul_of_nonneg_right h1 hb
      _ = b := one_mul b
      _ ≤ MaxCaterpillar.relu b := le_max_right 0 b
  · calc t * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 hb
      _ ≤ MaxCaterpillar.relu b := le_max_left 0 b

/-! ## (b) The support function -/

/-- **Support function of `pyr_{e_v}(B_{v,π,M})`.** -/
theorem paramidSupport_eq {M : Finset ℕ} (hM : M ⊆ Finset.Icc 2 (r + 1))
    (y : Fin (r + 1 + 1) → ℝ) :
    paramidSupport v π M y = y v + MaxCaterpillar.relu (y (π.pos (lastMarked M)) - y v +
      ∑ i in Finset.Icc 2 (r + 1),
        MaxCaterpillar.relu (y (π.pos (markedParent M i)) - y (π.pos i))) := by
  classical
  set b : ℕ → ℝ := fun i => y (π.pos (markedParent M i)) - y (π.pos i)
  set A : ℝ := y (π.pos (lastMarked M)) +
    ∑ i in Finset.Icc 2 (r + 1), MaxCaterpillar.relu (b i) with hA
  have hhull : paramid v π M ⊆ {p | evalL y p ≤ max (y v) A} := by
    apply convexHull_min _ (convex_halfspace_le (evalL y).isLinear _)
    refine Set.insert_subset_iff.mpr ⟨?_, ?_⟩
    · show evalL y (Pi.single v 1) ≤ _
      rw [evalL_single]
      exact le_max_left _ _
    · intro p hp
      rw [parallelepiped_eq_zonotope π hM] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      show evalL y (zvec π M t) ≤ _
      rw [evalL_zvec]
      refine le_max_of_le_right (add_le_add_left (Finset.sum_le_sum fun i hi => ?_) _)
      exact mul_le_relu (ht i hi).1 (ht i hi).2
  have hG : IsGreatest ((fun p => ∑ k, p k * y k) '' paramid v π M) (max (y v) A) := by
    refine ⟨?_, ?_⟩
    · by_cases hle : A ≤ y v
      · refine ⟨Pi.single v 1, subset_convexHull ℝ _ (Set.mem_insert _ _), ?_⟩
        show evalL y (Pi.single v 1) = _
        rw [evalL_single, max_eq_left hle]
      · let t : ℕ → ℝ := fun i => if 0 ≤ b i then 1 else 0
        have ht : ∀ i ∈ Finset.Icc 2 (r + 1), 0 ≤ t i ∧ t i ≤ 1 := fun i _ => by
          simp only [t]
          split_ifs <;> norm_num
        refine ⟨zvec π M t, subset_convexHull ℝ _
          (Set.mem_insert_of_mem _ (zvec_mem π hM t ht)), ?_⟩
        show evalL y (zvec π M t) = _
        rw [evalL_zvec, max_eq_right (le_of_not_le hle)]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        show t i * b i = MaxCaterpillar.relu (b i)
        simp only [t]
        split_ifs with h
        · rw [one_mul]
          exact (max_eq_right h).symm
        · rw [zero_mul]
          exact (max_eq_left (le_of_lt (not_le.mp h))).symm
    · rintro _ ⟨p, hp, rfl⟩
      exact hhull hp
  unfold paramidSupport supportFunction
  rw [hG.csSup_eq, MaxNN.max_eq_relu_add, add_comm]
  congr 1
  show MaxNN.relu _ = MaxNN.relu _
  congr 1
  rw [hA]
  ring

/-- With `M = ∅`: `q = 1` and `r ≡ 1`. -/
theorem paramidSupport_empty_eq (y : Fin (r + 1 + 1) → ℝ) :
    paramidSupport v π ∅ y = y v + MaxCaterpillar.relu (y (π.pos 1) - y v +
      ∑ i in Finset.Icc 2 (r + 1), MaxCaterpillar.relu (y (π.pos 1) - y (π.pos i))) := by
  rw [paramidSupport_eq π (Finset.empty_subset _), lastMarked_empty]
  simp only [markedParent_empty]

/-! ## The caterpillar function of a word -/

/-- `U_{π,S}(y) = σ(y_{π(q+1)} - y_{π(0)} + ∑_{j=1}^r σ(y_{π(p(j)+1)} - y_{π(j+1)}))`. -/
theorem caterpillarWordDescription_apply (σ : Equiv.Perm (Fin (r + 1 + 1)))
    (S : Finset (Fin (r + 1))) (y : Fin (r + 1 + 1) → ℝ) :
    caterpillarFunction (caterpillarWordDescription σ S) y =
      MaxCaterpillar.relu (y (σ (lastHead S).succ) - y (σ 0) +
        ∑ j : Fin r, MaxCaterpillar.relu (y (σ (parent S j.succ).succ) - y (σ j.succ.succ))) := by
  classical
  have hinj : Function.Injective (edgeVecs (rawBase σ) S) :=
    edgeVecs_simplex_injective (fun i => σ i.succ)
      (σ.injective.comp (Fin.succ_injective (r + 1))) S
  show realUnitY (rawGamma σ S, rawLabels σ S) y = _
  rw [realUnitY_eq_relu]
  unfold realUnitArg
  show MaxNN.relu _ = MaxNN.relu _
  congr 1
  change MaxNN.dot (rawBase σ (lastHead S) - rawApex σ) _ + ∑ v in Finset.univ.image
      (edgeVecs (rawBase σ) S), MaxNN.relu (MaxNN.dot v _) = _
  rw [Finset.sum_image (fun a _ b _ he => hinj he)]
  congr 1
  · unfold rawBase rawApex
    rw [MaxNN.SupportCut.dot_sub_left, MaxNN.Width.dot_toR_vtx_coordT,
      MaxNN.Width.dot_toR_vtx_coordT]
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    unfold edgeVecs rawBase
    rw [MaxNN.SupportCut.dot_sub_left, MaxNN.Width.dot_toR_vtx_coordT,
      MaxNN.Width.dot_toR_vtx_coordT]
    congr 1
    ring

/-- `((max' s : Fin) : ℕ) + 1 = max' t` when `s + 1 = t`. -/
theorem max'_succ_eq (s : Finset (Fin (r + 1))) (t : Finset ℕ) (hs : s.Nonempty)
    (ht : t.Nonempty) (h1 : ∀ y ∈ s, (y : ℕ) + 1 ∈ t) (h2 : ∀ x ∈ t, ∃ y ∈ s, x = (y : ℕ) + 1) :
    ((s.max' hs : Fin (r + 1)) : ℕ) + 1 = t.max' ht := by
  apply le_antisymm (Finset.le_max' t _ (h1 _ (Finset.max'_mem s hs)))
  obtain ⟨y, hy, he⟩ := h2 _ (Finset.max'_mem t ht)
  rw [he]
  exact Nat.succ_le_succ (Fin.le_iff_val_le_val.mp (Finset.le_max' s y hy))

section Dictionary

variable {M : Finset ℕ}

theorem mem_cutSet {j : Fin (r + 1)} : j ∈ cutSet M ↔ (j : ℕ) + 1 ∈ M := by
  unfold cutSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

theorem lastHead_cutSet (hM : M ⊆ Finset.Icc 2 (r + 1)) : ((lastHead (cutSet M) : Fin (r + 1)) : ℕ) + 1 = lastMarked M := by
  apply max'_succ_eq
  · intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (mem_cutSet.mp h)
  · intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact ⟨0, Finset.mem_insert_self _ _, h⟩
    · have hx' := Finset.mem_Icc.mp (hM h)
      refine ⟨⟨x - 1, by omega⟩, Finset.mem_insert_of_mem (mem_cutSet.mpr ?_), ?_⟩
      · show x - 1 + 1 ∈ M
        rwa [Nat.sub_add_cancel (by omega)]
      · show x = x - 1 + 1
        omega

theorem parent_cutSet (hM : M ⊆ Finset.Icc 2 (r + 1)) (j : Fin r) :
    ((parent (cutSet M) j.succ : Fin (r + 1)) : ℕ) + 1 = markedParent M ((j : ℕ) + 2) := by
  apply max'_succ_eq
  · intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]
      exact Finset.mem_insert_self _ _
    · have h' := Finset.mem_filter.mp h
      refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨mem_cutSet.mp h'.1, ?_⟩)
      have := Fin.lt_iff_val_lt_val.mp h'.2
      rw [Fin.val_succ] at this
      show (y : ℕ) + 1 < (j : ℕ) + 2
      exact Nat.succ_lt_succ this
  · intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact ⟨0, Finset.mem_insert_self _ _, h⟩
    · have h' := Finset.mem_filter.mp h
      have hx' := Finset.mem_Icc.mp (hM h'.1)
      have := hx'.1
      have := hx'.2
      refine ⟨⟨x - 1, by omega⟩, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨?_, ?_⟩), ?_⟩
      · apply mem_cutSet.mpr
        show x - 1 + 1 ∈ M
        rw [Nat.sub_add_cancel (by omega)]
        exact h'.1
      · rw [Fin.lt_iff_val_lt_val, Fin.val_succ]
        show x - 1 < (j : ℕ) + 1
        have h2 : x < (j : ℕ) + 2 := h'.2
        have h1x : 1 ≤ x := by omega
        apply Nat.lt_of_succ_lt_succ
        rw [Nat.succ_eq_add_one, Nat.sub_add_cancel h1x]
        exact h2
      · show x = x - 1 + 1
        omega

/-- `|S| = |M|`, so the sign `(-1)^{|M|}` of Brunck et al. is our `(-1)^{|S|}`. -/
theorem card_cutSet (hM : M ⊆ Finset.Icc 2 (r + 1)) : (cutSet (r := r) M).card = M.card := by
  refine Finset.card_congr (s := cutSet (r := r) M) (t := M) (fun j _ => (j : ℕ) + 1) ?_ ?_ ?_
  · intro j hj
    exact mem_cutSet.mp hj
  · intro a b _ _ h
    exact Fin.ext (by simpa using h)
  · intro x hx
    have hx' := Finset.mem_Icc.mp (hM hx)
    have := hx'.1
    have := hx'.2
    refine ⟨⟨x - 1, by omega⟩, mem_cutSet.mpr ?_, ?_⟩
    · show x - 1 + 1 ∈ M
      rwa [Nat.sub_add_cancel (by omega)]
    · show x - 1 + 1 = x
      omega

/-- **The dictionary.** `h_{pyr_{e_v}(B_{v,π,M})} = y_v + U_{π',S}` for the word
`π' = (v, π₁, …, π_{N-1})` and the cut set `S = M - 1`. -/
theorem paramidSupport_eq_word (hM : M ⊆ Finset.Icc 2 (r + 1)) (y : Fin (r + 1 + 1) → ℝ) :
    paramidSupport v π M y =
      y v + caterpillarFunction (caterpillarWordDescription π.word (cutSet M)) y := by
  rw [paramidSupport_eq π hM, caterpillarWordDescription_apply, word_succ, lastHead_cutSet hM,
    word_zero, sum_Icc_eq_fin]
  congr 3
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [word_succ, parent_cutSet hM, word_succ, Fin.val_succ]

theorem cutSet_mem_admissibleCuts (hM : M ⊆ Finset.Icc 2 (r + 1)) (hne : M.Nonempty) : cutSet (r := r) M ∈ admissibleCuts r := by
  unfold admissibleCuts cutPositions
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_powerset.mpr fun j hj => ?_⟩
  · obtain ⟨x, hx⟩ := hne
    have hx' := Finset.mem_Icc.mp (hM hx)
    have := hx'.1
    have := hx'.2
    intro h
    have hmem : (⟨x - 1, by omega⟩ : Fin (r + 1)) ∈ cutSet (r := r) M := by
      apply mem_cutSet.mpr
      show x - 1 + 1 ∈ M
      rwa [Nat.sub_add_cancel (by omega)]
    rw [h] at hmem
    exact Finset.not_mem_empty _ hmem
  · refine Finset.mem_erase.mpr ⟨fun h0 => ?_, Finset.mem_univ _⟩
    have := Finset.mem_Icc.mp (hM (mem_cutSet.mp hj))
    rw [h0, Fin.val_zero] at this
    obtain ⟨_, _⟩ := this
    omega

/-- For `M ≠ ∅` the support function is `y_v` plus a caterpillar function of `𝒦₀`. -/
theorem exists_caterpillarDescription (hM : M ⊆ Finset.Icc 2 (r + 1)) (hne : M.Nonempty) :
    ∃ k ∈ caterpillarDescriptions r,
      ∀ y, paramidSupport v π M y = y v + caterpillarFunction k y := by
  let w : WordIndex r := (π.word, ⟨cutSet M, cutSet_mem_admissibleCuts hM hne⟩)
  have hk0 : wordKey w ∈ correctionKeys r :=
    faceKeys_subset_correctionKeys w (self_mem_faceKeys _ _)
  refine ⟨normalizedKey (wordKey w), Finset.mem_image_of_mem _ hk0, fun y => ?_⟩
  rw [paramidSupport_eq_word π hM]
  show _ = y v + realUnitY (normalizedKey (wordKey w)) y
  rw [realUnitY_normalizedKey hk0]
  rfl

end Dictionary

/-! ## (c) The rooted stars -/

/-- **`M = ∅`.** The support function is `y_v` plus the rooted star `S_{v,π₁}`. -/
theorem paramidSupport_empty (y : Fin (r + 1 + 1) → ℝ) :
    paramidSupport v π ∅ y = y v + rootedStar v (π.pos 1) y := by
  classical
  rw [paramidSupport_empty_eq]
  unfold rootedStar
  congr 2
  have himage : (Finset.Icc 2 (r + 1)).image π.pos =
      (Finset.univ.erase v).erase (π.pos 1) := by
    ext l
    rw [Finset.mem_image, Finset.mem_erase, Finset.mem_erase]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' := Finset.mem_Icc.mp hi
      have := hi'.1
      have := hi'.2
      refine ⟨fun h => ?_, pos_ne π (by omega) hi'.2, Finset.mem_univ _⟩
      have := pos_inj π (by omega) hi'.2 (le_refl 1) (by omega) h
      omega
    · rintro ⟨h1, h2, -⟩
      obtain ⟨i, hi1, hi2, rfl⟩ := pos_surj π h2
      refine ⟨i, Finset.mem_Icc.mpr ⟨?_, hi2⟩, rfl⟩
      by_contra h
      exact h1 (by rw [show i = 1 by omega])
  rw [← himage, Finset.sum_image]
  · rfl
  · intro i hi j hj h
    exact pos_inj π (le_trans (by norm_num) (Finset.mem_Icc.mp hi).1) (Finset.mem_Icc.mp hi).2
      (le_trans (by norm_num) (Finset.mem_Icc.mp hj).1) (Finset.mem_Icc.mp hj).2 h

theorem single_apply_le_one {n : ℕ} (c z : Fin n) : (Pi.single c (1 : ℝ) : Fin n → ℝ) z ≤ 1 := by
  by_cases h : z = c
  · rw [h, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]
    norm_num

theorem single_apply_nonneg {n : ℕ} (c z : Fin n) :
    0 ≤ (Pi.single c (1 : ℝ) : Fin n → ℝ) z := by
  by_cases h : z = c
  · rw [h, Pi.single_eq_same]
    norm_num
  · rw [Pi.single_eq_of_ne h]

/-- A face function is at most its full caterpillar function. -/
theorem realUnitY_faceKey_le {n : ℕ} (γ : Fin n → ℝ) (V : Finset (Fin n → ℝ))
    (τ : V → Fin 3) (y : Fin (n + 1) → ℝ) :
    realUnitY (faceKey γ V τ) y ≤ realUnitY (γ, V) y := by
  classical
  unfold realUnitY MaxNN.ParamidGeom.paramidOn faceKey
  apply max_le_max le_rfl
  set Y := (MaxNN.ParamidGeom.CoordAux.coordT n).mulVec y
  have hdot : MaxNN.dot (γ + ∑ v in V.filter (fun v => keyExt V τ v = 1), v) Y =
      MaxNN.dot γ Y + ∑ v in V.filter (fun v => keyExt V τ v = 1), MaxNN.dot v Y := by
    rw [MaxNN.SupportCut.dot_add_left]
    congr 1
    simp only [MaxNN.dot, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hdot]
  have h1 : ∑ v in V.filter (fun v => keyExt V τ v = 1), MaxNN.dot v Y ≤
      ∑ v in V.filter (fun v => keyExt V τ v = 1), MaxNN.relu (MaxNN.dot v Y) :=
    Finset.sum_le_sum fun v _ => le_max_right _ _
  have h2 : ∑ v in V.filter (fun v => keyExt V τ v = 1), MaxNN.relu (MaxNN.dot v Y) +
      ∑ v in V.filter (fun v => keyExt V τ v = 2), MaxNN.relu (MaxNN.dot v Y) ≤
      ∑ v in V, MaxNN.relu (MaxNN.dot v Y) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have h0 := MaxNN.relu_nonneg (MaxNN.dot v Y)
    split_ifs with ha hb hb
    · rw [ha] at hb
      exact absurd hb (by decide)
    · linarith
    · linarith
    · linarith
  linarith

/-- Every caterpillar function is bounded by the function of a full word. -/
theorem caterpillarFunction_le_word {k : FaceKey r} (hk : k ∈ caterpillarDescriptions r)
    (y : Fin (r + 1 + 1) → ℝ) :
    ∃ σ S, S ∈ admissibleCuts r ∧
      caterpillarFunction k y ≤ caterpillarFunction (caterpillarWordDescription σ S) y := by
  obtain ⟨k0, hk0, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨kw, hkw, hkk⟩ := Finset.mem_biUnion.mp hk0
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hkw
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hkk
  refine ⟨w.1, w.2.1, w.2.2, ?_⟩
  show realUnitY (normalizedKey _) y ≤ realUnitY (wordGamma w, wordLabels w) y
  rw [realUnitY_normalizedKey hk0]
  exact realUnitY_faceKey_le _ _ τ y

/-- At `y = e_c` every full caterpillar function is at most `r = N - 2`. -/
theorem caterpillarWord_single_le (σ : Equiv.Perm (Fin (r + 1 + 1))) {S : Finset (Fin (r + 1))}
    (hS : S ∈ admissibleCuts r) (c : Fin (r + 1 + 1)) :
    caterpillarFunction (caterpillarWordDescription σ S) (Pi.single c 1) ≤ r := by
  classical
  rw [caterpillarWordDescription_apply]
  set y : Fin (r + 1 + 1) → ℝ := Pi.single c 1
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  apply max_le hr
  by_cases hc : σ 0 = c
  · have hy0 : y (σ 0) = 1 := by rw [hc]; exact Pi.single_eq_same c 1
    have hys : ∀ x : Fin (r + 1), y (σ x.succ) = 0 := fun x => by
      apply Pi.single_eq_of_ne
      intro h
      rw [← hc] at h
      exact Fin.succ_ne_zero x (σ.injective h)
    simp only [hy0, hys, sub_self]
    have : ∑ _j : Fin r, MaxCaterpillar.relu 0 = 0 :=
      Finset.sum_eq_zero fun _ _ => max_self 0
    rw [this]
    linarith
  · obtain ⟨x, hx⟩ : ∃ x : Fin (r + 1), σ x.succ = c := by
      have hne : σ.symm c ≠ 0 := fun h => hc (by rw [← h, Equiv.apply_symm_apply])
      exact ⟨(σ.symm c).pred hne, by rw [Fin.succ_pred, Equiv.apply_symm_apply]⟩
    have hy0 : y (σ 0) = 0 := Pi.single_eq_of_ne hc 1
    have hyx : ∀ z : Fin (r + 1), y (σ z.succ) = if z = x then 1 else 0 := fun z => by
      by_cases hz : z = x
      · rw [if_pos hz, hz, hx]
        exact Pi.single_eq_same c 1
      · rw [if_neg hz]
        apply Pi.single_eq_of_ne
        intro h
        rw [← hx] at h
        exact hz (Fin.succ_injective _ (σ.injective h))
    have hterm : ∀ j : Fin r, MaxCaterpillar.relu (y (σ (parent S j.succ).succ) - y (σ j.succ.succ))
        ≤ 1 - if j.succ = x then 1 else 0 := fun j => by
      have ha := single_apply_le_one c (σ (parent S j.succ).succ)
      rw [hyx j.succ]
      apply max_le
      · split_ifs <;> norm_num
      · split_ifs <;> linarith
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hsum
    rw [hy0, sub_zero]
    by_cases hx0 : x = 0
    · have hlast : lastHead S ≠ 0 := by
        have hS' := Finset.mem_erase.mp hS
        obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hS'.1
        have hs0 : s ≠ 0 := (Finset.mem_erase.mp (Finset.mem_powerset.mp hS'.2 hs)).1
        intro h
        have hle : s ≤ lastHead S := Finset.le_max' _ _ (Finset.mem_insert_of_mem hs)
        rw [h] at hle
        exact hs0 (le_antisymm hle (Fin.zero_le _))
      rw [hyx, if_neg (by rw [hx0]; exact hlast)]
      have hnn : 0 ≤ ∑ j : Fin r, (if j.succ = x then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
      linarith
    · obtain ⟨j0, rfl⟩ : ∃ j0 : Fin r, j0.succ = x := by
        have hxv : (x : ℕ) ≠ 0 := fun h => hx0 (Fin.ext h)
        have hxl : (x : ℕ) < r + 1 := x.isLt
        have h1x : 1 ≤ (x : ℕ) := Nat.pos_of_ne_zero hxv
        refine ⟨⟨(x : ℕ) - 1, Nat.lt_of_succ_lt_succ (by
          rw [Nat.succ_eq_add_one, Nat.sub_add_cancel h1x]
          exact hxl)⟩, Fin.ext ?_⟩
        rw [Fin.val_succ]
        exact Nat.sub_add_cancel h1x
      have hcount : ∑ j : Fin r, (if j.succ = j0.succ then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_eq_single j0]
        · rw [if_pos rfl]
        · intro b _ hb
          rw [if_neg (fun h => hb (Fin.succ_injective _ h))]
        · intro h
          exact absurd (Finset.mem_univ j0) h
      rw [hcount] at hsum
      have hA := single_apply_le_one c (σ (lastHead S).succ)
      linarith

/-- **Rooted stars are not caterpillar functions.** For `N = r + 2` and distinct `a, c`,
no caterpillar function equals the rooted star `S_{a,c}`: at `y = e_c` the star takes the
value `N - 1`, every caterpillar function at most `N - 2`. -/
theorem rootedStar_ne_caterpillarFunction {a c : Fin (r + 1 + 1)} (hac : a ≠ c)
    {k : FaceKey r} (hk : k ∈ caterpillarDescriptions r) :
    rootedStar a c ≠ caterpillarFunction k := by
  classical
  intro h
  obtain ⟨σ, S, hS, hle⟩ := caterpillarFunction_le_word hk (Pi.single c 1)
  have hb := caterpillarWord_single_le σ hS c
  rw [← h] at hle
  have hval : rootedStar a c (Pi.single c 1) = r + 1 := by
    unfold rootedStar
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hac]
    have hsum : ∑ l in (Finset.univ.erase a).erase c,
        MaxNN.relu (1 - (Pi.single c (1 : ℝ) : Fin (r + 1 + 1) → ℝ) l) = r := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) fun l hl => by
        show MaxNN.relu (1 - (Pi.single c (1 : ℝ) : Fin (r + 1 + 1) → ℝ) l) = 1
        rw [Pi.single_eq_of_ne (Finset.mem_erase.mp hl).1, sub_zero]
        exact MaxNN.relu_of_nonneg zero_le_one]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_univ c⟩),
        Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
      norm_num
    rw [hsum, sub_zero, MaxNN.relu_of_nonneg (by positivity)]
    ring
  rw [hval] at hle
  linarith

/-- For `M = ∅` the support function is not `y_v` plus any caterpillar function. -/
theorem paramidSupport_empty_not_caterpillar :
    ¬ ∃ k ∈ caterpillarDescriptions r,
      ∀ y, paramidSupport v π ∅ y = y v + caterpillarFunction k y := by
  rintro ⟨k, hk, h⟩
  apply rootedStar_ne_caterpillarFunction (pos_ne π (le_refl 1) (by omega)).symm hk
  funext y
  have := h y
  rw [paramidSupport_empty] at this
  linarith

/-- The word `σ` with apex `σ 0` as an ordering of `[N] ∖ {σ 0}`. -/
def orderingOfWord (σ : Equiv.Perm (Fin (r + 1 + 1))) : Ordering (r + 1 + 1) (σ 0) where
  toFun i := ⟨σ (Fin.succ i), fun h => Fin.succ_ne_zero _ (σ.injective h)⟩
  invFun k := (σ.symm k.1).pred fun h => k.2 (by rw [← Equiv.apply_symm_apply σ k.1, h])
  left_inv i := by
    simp only [Equiv.symm_apply_apply, Fin.pred_succ]
  right_inv k := by
    apply Subtype.ext
    simp only [Fin.succ_pred, Equiv.apply_symm_apply]

theorem word_orderingOfWord (σ : Equiv.Perm (Fin (r + 1 + 1))) :
    (orderingOfWord σ).word = σ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- **Converse.** Every caterpillar word `(σ, S)` is a pyramid of Brunck et al. with
`v = σ 0`, `π = (σ 1, …, σ (N-1))` and `M = S + 1 ≠ ∅`. -/
theorem exists_paramid_of_word (σ : Equiv.Perm (Fin (r + 1 + 1))) {S : Finset (Fin (r + 1))}
    (hS : S ∈ admissibleCuts r) :
    ∃ (v : Fin (r + 1 + 1)) (π : Ordering (r + 1 + 1) v) (M : Finset ℕ),
      M ⊆ Finset.Icc 2 (r + 1) ∧ M.Nonempty ∧ ∀ y,
        paramidSupport v π M y = y v + caterpillarFunction (caterpillarWordDescription σ S) y := by
  classical
  have hS' := Finset.mem_erase.mp hS
  have hsub : ∀ j ∈ S, j ≠ 0 := fun j hj =>
    (Finset.mem_erase.mp (Finset.mem_powerset.mp hS'.2 hj)).1
  let M : Finset ℕ := S.image fun j : Fin (r + 1) => (j : ℕ) + 1
  have hM : M ⊆ Finset.Icc 2 (r + 1) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have h0 : (j : ℕ) ≠ 0 := fun h => hsub j hj (Fin.ext h)
    have h1 : 1 ≤ (j : ℕ) := Nat.pos_of_ne_zero h0
    have h2 : (j : ℕ) ≤ r := Nat.lt_succ_iff.mp j.isLt
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_succ h1, Nat.succ_le_succ h2⟩
  have hcut : cutSet (r := r) M = S := by
    ext j
    rw [mem_cutSet, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, he⟩
      have he' : (i : ℕ) + 1 = (j : ℕ) + 1 := he
      rw [show j = i from Fin.ext (Nat.succ_injective he').symm]
      exact hi
    · intro hj
      exact ⟨j, hj, rfl⟩
  refine ⟨σ 0, orderingOfWord σ, M, hM, ?_, fun y => ?_⟩
  · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hS'.1
    exact ⟨_, Finset.mem_image_of_mem _ hs⟩
  · rw [paramidSupport_eq_word _ hM, word_orderingOfWord, hcut]

end MaxCaterpillar.BHRSY
