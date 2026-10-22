import MaxCaterpillar.CountExp.Defs

/-!
# The mixed finite difference (worker W1)

Steps 1–3 of `research/sN/NOTE.md`, "MAIN ROUTE", for the `k`-th mixed finite
difference `mixedDiff k B δ π` in the tie coordinates of a locality:

* `mixedDiff_auxiliary`: it kills the auxiliary span, since every neuron of the first
  hidden layer depends on at most two coordinates and the tie set has `k ≥ 3` elements;
* `mixedDiff_maximum`: on the box the maximum is `δ · [S ≠ ∅]`, so the mixed difference
  of the maximum is `-(-1)^k δ`;
* `pass_of_mixedDiff_unit_ne`: on a normalized face function the mixed difference is
  nonzero only if the preactivation vanishes at the base point and condition (s) holds.

The common tool is `mixedDiff_eq_zero_of_insert`: the mixed difference vanishes on a
function whose values on the box do not change when one tie coordinate moves.
-/

open BigOperators Finset

namespace MaxCaterpillar.CountExp

open MaxNN MaxNN.Width MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain CountCubic

/-! ## The box -/

section Box

variable {N : ℕ} {k B : ℕ} {δ : ℝ} {π : Equiv.Perm (Fin N)}

private theorem mem_tieSet {o : Fin N} : o ∈ tieSet k π ↔ ((π o : Fin N) : ℕ) < k := by
  unfold tieSet
  rw [mem_filter]
  exact and_iff_right (mem_univ o)

/-- The tie set has `k` elements (re-proved locally; W4 proves `card_tieSet`). -/
private theorem card_tieSet_W1 (hk : k ≤ N) (π : Equiv.Perm (Fin N)) :
    (tieSet k π).card = k := by
  have h : (tieSet k π).card = (range k).card := by
    apply Finset.card_congr (fun o _ => ((π o : Fin N) : ℕ))
    · intro o ho
      exact mem_range.mpr (mem_tieSet.mp ho)
    · intro a b _ _ h
      exact π.injective (Fin.ext h)
    · intro m hm
      have hm' := mem_range.mp hm
      refine ⟨π.symm ⟨m, by omega⟩, ?_, ?_⟩
      · rw [mem_tieSet, Equiv.apply_symm_apply]
        exact hm'
      · rw [Equiv.apply_symm_apply]
  rw [h, card_range]

private theorem basePtR_of_mem {o : Fin N} (ho : o ∈ tieSet k π) : basePtR k B π o = 0 := by
  unfold basePtR basePt
  rw [if_pos (mem_tieSet.mp ho)]
  norm_num

private theorem basePtR_le_neg_one (hB : 1 ≤ B) {o : Fin N} (ho : o ∉ tieSet k π) :
    basePtR k B π o ≤ -1 := by
  unfold basePtR basePt
  rw [if_neg (fun h => ho (mem_tieSet.mpr h))]
  push_cast
  have : (1 : ℝ) ≤ (B : ℝ) ^ ((π o : Fin N) : ℕ) :=
    one_le_pow_of_one_le (by exact_mod_cast hB) _
  linarith

private theorem basePtR_nonpos (o : Fin N) : basePtR k B π o ≤ 0 := by
  unfold basePtR basePt
  split_ifs
  · norm_num
  · push_cast
    have : (0 : ℝ) ≤ (B : ℝ) ^ ((π o : Fin N) : ℕ) := by positivity
    linarith

private theorem boxPt_of_mem {S : Finset (Fin N)} {o : Fin N} (ho : o ∈ tieSet k π) :
    boxPt k B δ π S o = if o ∈ S then δ else 0 := by
  unfold boxPt
  rw [basePtR_of_mem ho, zero_add]

private theorem boxPt_of_not_mem {S : Finset (Fin N)} (hS : S ⊆ tieSet k π) {o : Fin N}
    (ho : o ∉ tieSet k π) : boxPt k B δ π S o = basePtR k B π o := by
  unfold boxPt
  rw [if_neg (fun h => ho (hS h)), add_zero]

private theorem boxPt_le (S : Finset (Fin N)) (o : Fin N) :
    boxPt k B δ π S o ≤ if o ∈ S then δ else 0 := by
  unfold boxPt
  linarith [basePtR_nonpos (k := k) (B := B) (π := π) o]

private theorem boxPt_insert_of_ne {S : Finset (Fin N)} {t o : Fin N} (hot : o ≠ t) :
    boxPt k B δ π (insert t S) o = boxPt k B δ π S o := by
  unfold boxPt
  by_cases ho : o ∈ S
  · rw [if_pos (mem_insert_of_mem ho), if_pos ho]
  · rw [if_neg ho, if_neg (fun h => (mem_insert.mp h).elim hot ho)]

private theorem abs_boxPt_sub_le (hδ : 0 ≤ δ) (S : Finset (Fin N)) (o : Fin N) :
    |boxPt k B δ π S o - basePtR k B π o| ≤ δ := by
  unfold boxPt
  rw [add_sub_cancel']
  split_ifs
  · rw [abs_of_nonneg hδ]
  · rw [abs_zero]
    exact hδ

end Box

/-! ## The mixed difference vanishes on functions independent of a tie coordinate -/

section Core

variable {N : ℕ} {k B : ℕ} {δ : ℝ} {π : Equiv.Perm (Fin N)}

/-- The mixed difference only sees the values on the box. -/
private theorem mixedDiff_congr {g g' : (Fin N → ℝ) → ℝ}
    (h : ∀ S ⊆ tieSet k π, g (boxPt k B δ π S) = g' (boxPt k B δ π S)) :
    mixedDiff k B δ π g = mixedDiff k B δ π g' := by
  rw [mixedDiff_apply, mixedDiff_apply]
  exact sum_congr rfl fun S hS => by rw [h S (mem_powerset.mp hS)]

/-- **Core lemma.** If moving the tie coordinate `t` does not change the values on the
box, the mixed difference vanishes (pair `S` with `insert t S`). -/
private theorem mixedDiff_eq_zero_of_insert {g : (Fin N → ℝ) → ℝ} {t : Fin N}
    (ht : t ∈ tieSet k π)
    (h : ∀ S ⊆ tieSet k π, t ∉ S → g (boxPt k B δ π (insert t S)) = g (boxPt k B δ π S)) :
    mixedDiff k B δ π g = 0 := by
  rw [mixedDiff_apply]
  have hTe : tieSet k π = insert t ((tieSet k π).erase t) := (insert_erase ht).symm
  have hnot : t ∉ (tieSet k π).erase t := not_mem_erase t _
  rw [hTe, sum_powerset_insert hnot, ← sum_add_distrib]
  refine sum_eq_zero fun S hS => ?_
  have hS' : S ⊆ (tieSet k π).erase t := mem_powerset.mp hS
  have htS : t ∉ S := fun h => hnot (hS' h)
  have h1 : (insert t ((tieSet k π).erase t) \ S).card = ((tieSet k π).erase t \ S).card + 1 := by
    rw [insert_sdiff_of_not_mem _ htS,
      card_insert_of_not_mem (fun h => hnot (mem_sdiff.mp h).1)]
  have h2 : insert t ((tieSet k π).erase t) \ insert t S = (tieSet k π).erase t \ S := by
    rw [insert_sdiff_insert, sdiff_insert_of_not_mem hnot]
  rw [h1, h2, h S (hS'.trans (erase_subset t _)) htS, pow_succ]
  ring

/-- The mixed difference of order `k ≥ 3` kills every function of at most two
coordinates. -/
private theorem mixedDiff_eq_zero_of_two (hk : 3 ≤ k) (hkN : k ≤ N) {g : (Fin N → ℝ) → ℝ}
    (i j : Fin N) (hg : ∀ x x' : Fin N → ℝ, x i = x' i → x j = x' j → g x = g x') :
    mixedDiff k B δ π g = 0 := by
  have hc : 0 < (((tieSet k π).erase i).erase j).card := by
    have hle : ∀ (s : Finset (Fin N)) (a : Fin N), s.card ≤ (s.erase a).card + 1 := by
      intro s a
      by_cases h : a ∈ s
      · rw [card_erase_add_one h]
      · rw [erase_eq_of_not_mem h]
        exact Nat.le_succ _
    have h1 := hle (tieSet k π) i
    have h2 := hle ((tieSet k π).erase i) j
    rw [card_tieSet_W1 hkN π] at h1
    generalize (((tieSet k π).erase i).erase j).card = e2 at h2 ⊢
    generalize ((tieSet k π).erase i).card = e1 at h1 h2
    rcases Nat.eq_zero_or_pos e2 with h | h
    · subst h
      omega
    · exact h
  obtain ⟨t, ht⟩ := card_pos.mp hc
  have htj : t ≠ j := ne_of_mem_erase ht
  have hti : t ≠ i := ne_of_mem_erase (mem_of_mem_erase ht)
  have htT : t ∈ tieSet k π := mem_of_mem_erase (mem_of_mem_erase ht)
  refine mixedDiff_eq_zero_of_insert htT fun S _ _ => hg _ _ ?_ ?_
  · exact boxPt_insert_of_ne (Ne.symm hti)
  · exact boxPt_insert_of_ne (Ne.symm htj)

/-- The signs of the mixed difference sum to zero. -/
private theorem sum_sign_eq_zero (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∑ S in (tieSet k π).powerset, (-1 : ℝ) ^ (tieSet k π \ S).card = 0 := by
  have hc : 0 < (tieSet k π).card := by rw [card_tieSet_W1 hkN π]; omega
  obtain ⟨t, ht⟩ := card_pos.mp hc
  have h := mixedDiff_eq_zero_of_insert (B := 0) (δ := 0) (g := fun _ => (1 : ℝ)) ht
    (fun _ _ _ => rfl)
  rw [mixedDiff_apply] at h
  simpa only [mul_one] using h

end Core

/-! ## Step 1: the auxiliary span -/

section Auxiliary

variable {N : ℕ} {k B : ℕ} {δ : ℝ} {π : Equiv.Perm (Fin N)}

/-- Every neuron of the first hidden layer is killed. -/
private theorem mixedDiff_feat (hk : 3 ≤ k) (hkN : k ≤ N) (j : Fin (W N)) :
    mixedDiff k B δ π (fun x => feat N x j) = 0 := by
  refine Fin.addCases (motive := fun j : Fin (N + (N + N.choose 2)) =>
      mixedDiff k B δ π (fun x => feat N x j) = 0) (fun i => ?_) (fun j => ?_) j
  · refine mixedDiff_eq_zero_of_two hk hkN i i fun x x' hi _ => ?_
    show feat N x (posIdx i) = feat N x' (posIdx i)
    rw [feat_pos, feat_pos, hi]
  · refine Fin.addCases (motive := fun j : Fin (N + N.choose 2) =>
      mixedDiff k B δ π (fun x => feat N x (Fin.natAdd _ j)) = 0)
      (fun i => ?_) (fun q => ?_) j
    · refine mixedDiff_eq_zero_of_two hk hkN i i fun x x' hi _ => ?_
      show feat N x (negIdx i) = feat N x' (negIdx i)
      rw [feat_neg, feat_neg, hi]
    · refine mixedDiff_eq_zero_of_two hk hkN (prFst q) (prSnd q) fun x x' h1 h2 => ?_
      show feat N x (prIdx q) = feat N x' (prIdx q)
      rw [feat_pr, feat_pr, h1, h2]

/-- **Step 1.** The mixed difference kills the auxiliary span. -/
theorem mixedDiff_auxiliary {r k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) (B : ℕ) (δ : ℝ)
    (π : Equiv.Perm (Fin (r + 1 + 1))) (a : Fin (Width.W (r + 1 + 1)) → ℝ) :
    mixedDiff k B δ π (auxiliary a) = 0 := by
  have he : auxiliary a =
      ∑ j, a j • (fun x : Fin (r + 1 + 1) → ℝ => feat (r + 1 + 1) x j) := by
    funext x
    rw [Finset.sum_apply]
    rfl
  rw [he, map_sum]
  refine sum_eq_zero fun j _ => ?_
  rw [map_smul, mixedDiff_feat hk hkN j, smul_zero]

end Auxiliary

/-! ## Step 2: the maximum -/

/-- On the box the maximum is `δ · [S ≠ ∅]`, so the mixed difference is `-(-1)^k δ`. -/
theorem mixedDiff_maximum {r k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ r + 1 + 1) {B : ℕ} (hB : 1 ≤ B)
    {δ : ℝ} (hδ : 0 ≤ δ) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    mixedDiff k B δ π (Maximum (r + 1 + 1)) = -(-1) ^ k * δ := by
  have hc : 0 < (tieSet k π).card := by rw [card_tieSet_W1 hkN π]; omega
  obtain ⟨t, ht⟩ := card_pos.mp hc
  have hval : ∀ S ⊆ tieSet k π,
      Maximum (r + 1 + 1) (boxPt k B δ π S) = δ - if S = ∅ then δ else 0 := by
    intro S hS
    unfold Maximum
    by_cases he : S = ∅
    · rw [if_pos he, sub_self]
      refine le_antisymm (Finset.sup'_le _ _ fun o _ => ?_) ?_
      · have := boxPt_le (k := k) (B := B) (δ := δ) (π := π) S o
        rwa [if_neg (by rw [he]; exact not_mem_empty o)] at this
      · refine le_trans (le_of_eq ?_) (Finset.le_sup' (boxPt k B δ π S) (mem_univ t))
        rw [boxPt_of_mem ht, he, if_neg (not_mem_empty t)]
    · rw [if_neg he, sub_zero]
      obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.mpr he
      refine le_antisymm (Finset.sup'_le _ _ fun o _ => ?_) ?_
      · refine (boxPt_le S o).trans ?_
        split_ifs
        · exact le_rfl
        · exact hδ
      · refine le_trans (le_of_eq ?_) (Finset.le_sup' (boxPt k B δ π S) (mem_univ s))
        rw [boxPt_of_mem (hS hs), if_pos hs]
  have hsum : ∑ S in (tieSet k π).powerset,
      (-1 : ℝ) ^ (tieSet k π \ S).card * Maximum (r + 1 + 1) (boxPt k B δ π S) =
      ∑ S in (tieSet k π).powerset,
        (-1 : ℝ) ^ (tieSet k π \ S).card * (δ - if S = ∅ then δ else 0) :=
    sum_congr rfl fun S hS => by rw [hval S (mem_powerset.mp hS)]
  rw [mixedDiff_apply, hsum]
  simp only [mul_sub, sum_sub_distrib, mul_ite, mul_zero]
  rw [← sum_mul, sum_sign_eq_zero hk hkN, zero_mul, sum_ite_eq', if_pos (empty_mem_powerset _),
    sdiff_empty, card_tieSet_W1 hkN π]
  ring

/-! ## Step 3: face functions -/

section Units

variable {r : ℕ}

/-- `MaxCaterpillar.relu` (used by `realUnitArg_eq`) on a nonnegative argument. -/
private theorem crelu_of_nonneg {x : ℝ} (hx : 0 ≤ x) : MaxCaterpillar.relu x = x :=
  max_eq_right hx

private theorem crelu_of_nonpos {x : ℝ} (hx : x ≤ 0) : MaxCaterpillar.relu x = 0 :=
  max_eq_left hx

private theorem relu_intCast (m : ℤ) : ∃ z : ℤ, relu (m : ℝ) = z := by
  rcases le_total 0 m with h | h
  · exact ⟨m, crelu_of_nonneg (by exact_mod_cast h)⟩
  · exact ⟨0, by rw [crelu_of_nonpos (by exact_mod_cast h)]; norm_num⟩

private theorem abs_relu_sub_le (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  rw [max_comm 0 a, max_comm 0 b]
  exact abs_max_sub_max_le_abs a b 0

/-- The preactivation is an integer at the integer base point. -/
private theorem realUnitArg_basePtR_isInt {key : RealKey (r + 1)}
    (hkey : key ∈ normalizedKeys r)
    (k B : ℕ) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    ∃ z : ℤ, realUnitArg key (basePtR k B π) = z := by
  choose hz hhz using keyHead_isInt hkey
  choose f hf using fun p : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
    relu_intCast (basePt k B π p.1 - basePt k B π p.2)
  refine ⟨∑ o, hz o * basePt k B π o + ∑ p in pairSet key, f p, ?_⟩
  rw [realUnitArg_eq hkey]
  push_cast
  congr 1
  · exact sum_congr rfl fun o _ => by rw [hhz o]; rfl
  · refine sum_congr rfl fun p _ => ?_
    rw [← hf p]
    push_cast
    rfl

/-- On the box the preactivation moves by at most `δ (∑ |h| + 2 |M|)`. -/
private theorem abs_realUnitArg_boxPt_sub_le {key : RealKey (r + 1)}
    (hkey : key ∈ normalizedKeys r)
    {k B : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (π : Equiv.Perm (Fin (r + 1 + 1)))
    (S : Finset (Fin (r + 1 + 1))) :
    |realUnitArg key (boxPt k B δ π S) - realUnitArg key (basePtR k B π)| ≤
      δ * (∑ o, |keyHead key o| + 2 * ((pairSet key).card : ℝ)) := by
  have he := abs_boxPt_sub_le (k := k) (B := B) (π := π) hδ S
  rw [realUnitArg_eq hkey, realUnitArg_eq hkey]
  have h1 : |∑ o, keyHead key o * boxPt k B δ π S o - ∑ o, keyHead key o * basePtR k B π o| ≤
      δ * ∑ o, |keyHead key o| := by
    rw [← sum_sub_distrib, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun o _ => ?_)
    rw [← mul_sub, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (he o) (abs_nonneg _)
  have h2 : |∑ p in pairSet key, relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) -
      ∑ p in pairSet key, relu (basePtR k B π p.1 - basePtR k B π p.2)| ≤
      δ * (2 * ((pairSet key).card : ℝ)) := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hp : ∀ p ∈ pairSet key, |relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) -
        relu (basePtR k B π p.1 - basePtR k B π p.2)| ≤ 2 * δ := by
      intro p _
      refine (abs_relu_sub_le _ _).trans ?_
      have e1 := abs_le.mp (he p.1)
      have e2 := abs_le.mp (he p.2)
      rw [abs_le]
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
    refine (sum_le_sum hp).trans (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul]
    ring
  calc _ = |(∑ o, keyHead key o * boxPt k B δ π S o - ∑ o, keyHead key o * basePtR k B π o) +
        (∑ p in pairSet key, relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) -
          ∑ p in pairSet key, relu (basePtR k B π p.1 - basePtR k B π p.2))| := by
          congr 1
          ring
    _ ≤ _ := (abs_add _ _).trans (add_le_add h1 h2)
    _ = _ := by ring

/-- The preactivation of a normalized key is killed (it is a sum of functions of at most
two coordinates). -/
private theorem mixedDiff_realUnitArg {key : RealKey (r + 1)} (hkey : key ∈ normalizedKeys r)
    {k B : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    mixedDiff k B δ π (realUnitArg key) = 0 := by
  have he : realUnitArg key =
      (∑ o, keyHead key o • (fun y : Fin (r + 1 + 1) → ℝ => y o)) +
        ∑ p in pairSet key, (fun y : Fin (r + 1 + 1) → ℝ => relu (y p.1 - y p.2)) := by
    funext y
    rw [realUnitArg_eq hkey, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
    rfl
  rw [he, map_add, map_sum, map_sum]
  rw [sum_eq_zero fun o _ => ?_, sum_eq_zero fun p _ => ?_, add_zero]
  · exact mixedDiff_eq_zero_of_two hk hkN p.1 p.2 fun x x' h1 h2 => by
      show relu (x p.1 - x p.2) = relu (x' p.1 - x' p.2)
      rw [h1, h2]
  · rw [map_smul, mixedDiff_eq_zero_of_two hk hkN o o fun x x' h _ => h, smul_zero]

/-- `κ_t = h_t + #{(t, x) ∈ M}`. -/
private theorem kappa_eq_card_filter (key : RealKey (r + 1)) (t : Fin (r + 1 + 1)) :
    kappa key t = keyHead key t + (((pairSet key).filter fun p => p.1 = t).card : ℝ) := by
  unfold kappa
  congr 2
  have he : (pairSet key).filter (fun p => p.1 = t) = (upNbrs key t).image (Prod.mk t) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, mem_pairSet, Finset.mem_image, mem_upNbrs, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hab, hp⟩, rfl⟩
      exact ⟨b, ⟨hab, hp⟩, rfl, rfl⟩
    · rintro ⟨x, ⟨hx, hp⟩, rfl, rfl⟩
      exact ⟨⟨hx, hp⟩, rfl⟩
  rw [he, card_image_of_injective _ (Prod.mk.inj_left t)]

/-- If the tie coordinate `t` has no neighbour in the tie set and `κ_t = 0`, moving `t`
does not change the preactivation on the box. -/
private theorem realUnitArg_boxPt_insert {key : RealKey (r + 1)}
    (hkey : key ∈ normalizedKeys r)
    {k B : ℕ} (hB : 1 ≤ B) {δ : ℝ} (hδ : 0 ≤ δ) {π : Equiv.Perm (Fin (r + 1 + 1))}
    {t : Fin (r + 1 + 1)} (ht : t ∈ tieSet k π)
    (hnb : ∀ x, ((π x : Fin (r + 1 + 1)) : ℕ) < k → ¬ HingeNbr key t x)
    (hκ : kappa key t = 0) {S : Finset (Fin (r + 1 + 1))} (hS : S ⊆ tieSet k π) (htS : t ∉ S) :
    realUnitArg key (boxPt k B δ π (insert t S)) = realUnitArg key (boxPt k B δ π S) := by
  have hS' : insert t S ⊆ tieSet k π := insert_subset_iff.mpr ⟨ht, hS⟩
  have hy't : boxPt k B δ π (insert t S) t = δ := by
    rw [boxPt_of_mem ht, if_pos (mem_insert_self t S)]
  have hyt : boxPt k B δ π S t = 0 := by
    rw [boxPt_of_mem ht, if_neg htS]
  have hout : ∀ x, HingeNbr key t x → x ∉ tieSet k π := fun x hx hxT =>
    hnb x (mem_tieSet.mp hxT) hx
  have hlin : ∑ o, keyHead key o * boxPt k B δ π (insert t S) o =
      ∑ o, keyHead key o * boxPt k B δ π S o + keyHead key t * δ := by
    have hd : ∀ o, keyHead key o * boxPt k B δ π (insert t S) o =
        keyHead key o * boxPt k B δ π S o + if o = t then keyHead key t * δ else 0 := by
      intro o
      by_cases hot : o = t
      · subst hot
        rw [hy't, hyt, if_pos rfl]
        ring
      · rw [boxPt_insert_of_ne hot, if_neg hot, add_zero]
    rw [sum_congr rfl fun o _ => hd o, sum_add_distrib, sum_ite_eq', if_pos (mem_univ t)]
  have hpair : ∑ p in pairSet key,
        relu (boxPt k B δ π (insert t S) p.1 - boxPt k B δ π (insert t S) p.2) =
      ∑ p in pairSet key, relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) +
        δ * (((pairSet key).filter fun p => p.1 = t).card : ℝ) := by
    have hd : ∀ p ∈ pairSet key,
        relu (boxPt k B δ π (insert t S) p.1 - boxPt k B δ π (insert t S) p.2) =
          relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) + if p.1 = t then δ else 0 := by
      intro p hp
      have hhp := (mem_pairSet.mp hp).2
      by_cases h1 : p.1 = t
      · have h2T : p.2 ∉ tieSet k π := hout p.2 (Or.inl (h1 ▸ hhp))
        rw [if_pos h1, h1, hy't, hyt, boxPt_of_not_mem hS' h2T, boxPt_of_not_mem hS h2T]
        have hb := basePtR_le_neg_one (k := k) (π := π) hB h2T
        rw [crelu_of_nonneg (by linarith), crelu_of_nonneg (by linarith)]
        ring
      · rw [if_neg h1, add_zero]
        by_cases h2 : p.2 = t
        · have h1T : p.1 ∉ tieSet k π := hout p.1 (Or.inr (h2 ▸ hhp))
          rw [h2, hy't, hyt, boxPt_of_not_mem hS' h1T, boxPt_of_not_mem hS h1T]
          have hb := basePtR_le_neg_one (k := k) (π := π) hB h1T
          rw [crelu_of_nonpos (by linarith), crelu_of_nonpos (by linarith)]
        · rw [boxPt_insert_of_ne h1, boxPt_insert_of_ne h2]
    rw [sum_congr rfl hd, sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have hκ' := kappa_eq_card_filter key t
  rw [realUnitArg_eq hkey, realUnitArg_eq hkey, hlin, hpair]
  have : keyHead key t * δ + δ * (((pairSet key).filter fun p => p.1 = t).card : ℝ) =
      δ * kappa key t := by
    rw [hκ']
    ring
  rw [hκ, mul_zero] at this
  linarith

/-- **Steps 2–3.** If the mixed difference does not vanish on a normalized face function,
its preactivation vanishes at the base point and condition (s) holds. -/
theorem pass_of_mixedDiff_unit_ne {r k B : ℕ} {δ : ℝ} {key : RealKey (r + 1)}
    (hkey : key ∈ normalizedKeys r) (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) (hB : 1 ≤ B)
    (hδ : 0 < δ) (hδb : δ * (∑ o, |keyHead key o| + 2 * ((pairSet key).card : ℝ)) < 1)
    (π : Equiv.Perm (Fin (r + 1 + 1)))
    (hne : mixedDiff k B δ π (realUnitY key) ≠ 0) :
    realUnitArg key (basePtR k B π) = 0 ∧ Active (HingeNbr key) (kappa key) k π := by
  obtain ⟨z, hz⟩ := realUnitArg_basePtR_isInt hkey k B π
  have hb : ∀ S, |realUnitArg key (boxPt k B δ π S) - z| < 1 := fun S => by
    rw [← hz]
    exact (abs_realUnitArg_boxPt_sub_le hkey hδ.le π S).trans_lt hδb
  rcases lt_trichotomy z 0 with hz0 | hz0 | hz0
  · -- the face function vanishes on the box
    exfalso
    apply hne
    rw [mixedDiff_congr (g' := 0) fun S _ => ?_, map_zero]
    have h := abs_lt.mp (hb S)
    have hz1 : (z : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hz0
    rw [realUnitY_eq_relu, relu_of_nonpos (by linarith [h.2]), Pi.zero_apply]
  · refine ⟨by rw [hz, hz0, Int.cast_zero], ?_⟩
    intro t htk hnb
    intro hκ
    apply hne
    have ht : t ∈ tieSet k π := mem_tieSet.mpr htk
    refine mixedDiff_eq_zero_of_insert ht fun S hS htS => ?_
    rw [realUnitY_eq_relu, realUnitY_eq_relu,
      realUnitArg_boxPt_insert hkey hB hδ.le ht hnb hκ hS htS]
  · -- the face function equals its preactivation on the box
    exfalso
    apply hne
    rw [mixedDiff_congr (g' := realUnitArg key) fun S _ => ?_,
      mixedDiff_realUnitArg hkey hk hkN π]
    have h := abs_lt.mp (hb S)
    have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz0
    rw [realUnitY_eq_relu, relu_of_nonneg (by linarith [h.1])]

end Units

end MaxCaterpillar.CountExp
