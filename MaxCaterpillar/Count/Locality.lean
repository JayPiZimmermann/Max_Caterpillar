import MaxCaterpillar.Compilation
import Mathlib.LinearAlgebra.Pi

/-!
# Localities and the mixed finite difference

A *locality* of a permutation `π` of the coordinates and `k ≤ N` is the tie set
`T = {o : π o < k}` with the base point `0` on `T` and `-B^(π o)` elsewhere.  The `k`-th
mixed finite difference at the base point (`mixedDiff`) kills the auxiliary functions
(`mixedDiff_auxiliary`), takes the value `-(-1)^k δ` on the maximum (`mixedDiff_maximum`),
and kills every function that does not depend on some tie coordinate.  The digit argument
(`digits_eq_zero`, `basePtR_anti`) and the fiber count (`card_fiber_pairsOrdered`) are the
two combinatorial inputs of the per-unit counts.
-/

open BigOperators Finset

namespace MaxCaterpillar.Count

open MaxNN MaxNN.Width MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain

/-! ## Localities and the mixed finite difference -/

section Locality

variable {N : ℕ}

/-- The tie set `T = {o : π o < k}` of the locality of `π`. -/
def tieSet (k : ℕ) (π : Equiv.Perm (Fin N)) : Finset (Fin N) :=
  univ.filter fun o => ((π o : Fin N) : ℕ) < k

/-- The permutations whose tie set is `T`. -/
def fiber (k : ℕ) (T : Finset (Fin N)) : Finset (Equiv.Perm (Fin N)) :=
  univ.filter fun π => tieSet k π = T

/-- The integer base point of the locality: `0` on the tie set and `-B^(π o)`
at every other coordinate. -/
def basePt (k B : ℕ) (π : Equiv.Perm (Fin N)) (o : Fin N) : ℤ :=
  if ((π o : Fin N) : ℕ) < k then 0 else -((B : ℤ) ^ ((π o : Fin N) : ℕ))

/-- The base point as a real point. -/
noncomputable def basePtR (k B : ℕ) (π : Equiv.Perm (Fin N)) (o : Fin N) : ℝ :=
  (basePt k B π o : ℝ)

/-- A corner of the box of side `δ` at the base point: `δ` is added on `S`. -/
noncomputable def boxPt (k B : ℕ) (δ : ℝ) (π : Equiv.Perm (Fin N)) (S : Finset (Fin N))
    (o : Fin N) : ℝ :=
  basePtR k B π o + if o ∈ S then δ else 0

/-- The `k`-th mixed finite difference in the tie coordinates, at the base point,
with step `δ`: `g ↦ ∑_{S ⊆ T} (-1)^{|T \ S|} g (boxPt S)`. -/
noncomputable def mixedDiff (k B : ℕ) (δ : ℝ) (π : Equiv.Perm (Fin N)) :
    ((Fin N → ℝ) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ S in (tieSet k π).powerset,
    ((-1 : ℝ) ^ (tieSet k π \ S).card) •
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin N → ℝ => ℝ) (boxPt k B δ π S)

theorem mixedDiff_apply (k B : ℕ) (δ : ℝ) (π : Equiv.Perm (Fin N)) (g : (Fin N → ℝ) → ℝ) :
    mixedDiff k B δ π g =
      ∑ S in (tieSet k π).powerset, (-1 : ℝ) ^ (tieSet k π \ S).card * g (boxPt k B δ π S) := by
  unfold mixedDiff
  rw [LinearMap.coeFn_sum, Finset.sum_apply]
  rfl

end Locality

/-! ## The pass conditions -/

section Pass

variable {N : ℕ}

/-- The number of `adj`-neighbours of `o` at a smaller position (above `o`). -/
noncomputable def upCount (adj : Fin N → Fin N → Prop) (π : Equiv.Perm (Fin N)) (o : Fin N) :
    ℕ := by
  classical
  exact (univ.filter fun x => adj o x ∧ π x < π o).card

/-- Condition (a): every coordinate outside the tie set has exactly `κ_o`
neighbours above it. -/
def Balanced (adj : Fin N → Fin N → Prop) (κ : Fin N → ℝ) (k : ℕ) (π : Equiv.Perm (Fin N)) :
    Prop :=
  ∀ o, k ≤ ((π o : Fin N) : ℕ) → (upCount adj π o : ℝ) = κ o

/-- Condition (s): every tie coordinate without a neighbour in the tie set has
`κ_t ≠ 0`. -/
def Active (adj : Fin N → Fin N → Prop) (κ : Fin N → ℝ) (k : ℕ) (π : Equiv.Perm (Fin N)) :
    Prop :=
  ∀ t, ((π t : Fin N) : ℕ) < k → (∀ x, ((π x : Fin N) : ℕ) < k → ¬ adj t x) → κ t ≠ 0

end Pass

/-! ## The box -/

section Box

variable {N : ℕ} {k B : ℕ} {δ : ℝ} {π : Equiv.Perm (Fin N)}

theorem mem_tieSet {o : Fin N} :
    o ∈ tieSet k π ↔ ((π o : Fin N) : ℕ) < k := by
  simp [tieSet]

theorem card_tieSet (hk : k ≤ N) (π : Equiv.Perm (Fin N)) :
    (tieSet k π).card = k := by
  have h : (tieSet k π).map (π.toEmbedding.trans Fin.valEmbedding) = range k := by
    ext n
    simp only [mem_map, mem_tieSet, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ho
    · intro hn
      refine ⟨π.symm ⟨n, by omega⟩, ?_, ?_⟩ <;> simp [hn]
  have := congrArg Finset.card h
  rwa [card_map, card_range] at this

theorem basePtR_of_mem {o : Fin N} (ho : o ∈ tieSet k π) : basePtR k B π o = 0 := by
  unfold basePtR basePt
  rw [if_pos (mem_tieSet.mp ho)]
  norm_num

theorem basePtR_nonpos (o : Fin N) : basePtR k B π o ≤ 0 := by
  unfold basePtR basePt
  split_ifs
  · norm_num
  · push_cast
    have : (0 : ℝ) ≤ (B : ℝ) ^ ((π o : Fin N) : ℕ) := by positivity
    linarith

theorem boxPt_of_mem {S : Finset (Fin N)} {o : Fin N} (ho : o ∈ tieSet k π) :
    boxPt k B δ π S o = if o ∈ S then δ else 0 := by
  unfold boxPt
  rw [basePtR_of_mem ho, zero_add]

theorem boxPt_le (S : Finset (Fin N)) (o : Fin N) :
    boxPt k B δ π S o ≤ if o ∈ S then δ else 0 := by
  unfold boxPt
  linarith [basePtR_nonpos (k := k) (B := B) (π := π) o]

theorem boxPt_insert_of_ne {S : Finset (Fin N)} {t o : Fin N} (hot : o ≠ t) :
    boxPt k B δ π (insert t S) o = boxPt k B δ π S o := by
  unfold boxPt
  by_cases ho : o ∈ S
  · rw [if_pos (mem_insert_of_mem ho), if_pos ho]
  · rw [if_neg ho, if_neg (fun h => (mem_insert.mp h).elim hot ho)]

theorem basePtR_le_neg_one (hB : 1 ≤ B) {o : Fin N} (ho : o ∉ tieSet k π) :
    basePtR k B π o ≤ -1 := by
  unfold basePtR basePt
  rw [if_neg (fun h => ho (mem_tieSet.mpr h))]
  push_cast
  have : (1 : ℝ) ≤ (B : ℝ) ^ ((π o : Fin N) : ℕ) :=
    one_le_pow_of_one_le (by exact_mod_cast hB) _
  linarith

theorem boxPt_of_not_mem {S : Finset (Fin N)} (hS : S ⊆ tieSet k π) {o : Fin N}
    (ho : o ∉ tieSet k π) : boxPt k B δ π S o = basePtR k B π o := by
  unfold boxPt
  rw [if_neg (fun h => ho (hS h)), add_zero]

end Box

/-! ## The mixed difference vanishes on functions independent of a tie coordinate -/

section Core

variable {N : ℕ} {k B : ℕ} {δ : ℝ} {π : Equiv.Perm (Fin N)}

/-- **Core lemma.** If moving the tie coordinate `t` does not change the values on the
box, the mixed difference vanishes (pair `S` with `insert t S`). -/
theorem mixedDiff_eq_zero_of_insert {g : (Fin N → ℝ) → ℝ} {t : Fin N}
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
theorem mixedDiff_eq_zero_of_two (hk : 3 ≤ k) (hkN : k ≤ N) {g : (Fin N → ℝ) → ℝ}
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
    rw [card_tieSet hkN π] at h1
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
theorem sum_sign_eq_zero (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∑ S in (tieSet k π).powerset, (-1 : ℝ) ^ (tieSet k π \ S).card = 0 := by
  have hc : 0 < (tieSet k π).card := by rw [card_tieSet hkN π]; omega
  obtain ⟨t, ht⟩ := card_pos.mp hc
  have h := mixedDiff_eq_zero_of_insert (B := 0) (δ := 0) (g := fun _ => (1 : ℝ)) ht
    (fun _ _ _ => rfl)
  rw [mixedDiff_apply] at h
  simpa only [mul_one] using h

theorem mixedDiff_congr {g g' : (Fin N → ℝ) → ℝ}
    (h : ∀ S ⊆ tieSet k π, g (boxPt k B δ π S) = g' (boxPt k B δ π S)) :
    mixedDiff k B δ π g = mixedDiff k B δ π g' := by
  rw [mixedDiff_apply, mixedDiff_apply]
  exact sum_congr rfl fun S hS => by rw [h S (mem_powerset.mp hS)]

end Core

/-! ## Step 1: the auxiliary span -/

section Auxiliary

variable {N : ℕ} {k B : ℕ} {δ : ℝ} {π : Equiv.Perm (Fin N)}

/-- Every neuron of the first hidden layer is killed. -/
theorem mixedDiff_feat (hk : 3 ≤ k) (hkN : k ≤ N) (j : Fin (W N)) :
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
  have hc : 0 < (tieSet k π).card := by rw [card_tieSet hkN π]; omega
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
    sdiff_empty, card_tieSet hkN π]
  ring

/-- Signed digits: integers `c_o` with `|c_o| < B` at distinct exponents whose
weighted sum `∑ c_o B^{e o}` vanishes are all zero. -/
theorem digits_eq_zero {ι : Type*} [DecidableEq ι] {B : ℤ} (hB : 0 < B) (e : ι → ℕ)
    (c : ι → ℤ) (S : Finset ι) (he : Set.InjOn e S) (hc : ∀ o ∈ S, |c o| < B)
    (hsum : ∑ o in S, c o * B ^ e o = 0) : ∀ o ∈ S, c o = 0 := by
  revert he hc hsum
  refine Finset.induction_on_min_value e S ?_ ?_
  · intro _ _ _ o ho; exact absurd ho (Finset.not_mem_empty o)
  · intro a s has hmin ih he hc hsum
    rw [Finset.sum_insert has] at hsum
    have hdvd : B ^ (e a + 1) ∣ ∑ x in s, c x * B ^ e x := by
      apply Finset.dvd_sum
      intro x hx
      have hxa : x ≠ a := fun h => has (h ▸ hx)
      have hlt : e a < e x := lt_of_le_of_ne (hmin x hx) (fun h =>
        hxa (he (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hx))
          (Finset.mem_coe.mpr (Finset.mem_insert_self a s)) h.symm))
      exact Dvd.dvd.mul_left (pow_dvd_pow B hlt) _
    have hca : c a = 0 := by
      have h1 : B ^ (e a + 1) ∣ c a * B ^ e a := by
        have : c a * B ^ e a = -(∑ x in s, c x * B ^ e x) := by linarith
        rw [this]; exact (dvd_neg).mpr hdvd
      have h2 : B ∣ c a := by
        have hpow : B ^ (e a + 1) = B * B ^ e a := by ring
        rw [hpow] at h1
        exact (mul_dvd_mul_iff_right (pow_ne_zero _ hB.ne')).mp h1
      exact Int.eq_zero_of_abs_lt_dvd h2 (hc a (Finset.mem_insert_self a s))
    rw [hca, zero_mul, zero_add] at hsum
    have hrest := ih (he.mono (Finset.coe_subset.mpr (Finset.subset_insert a s)))
      (fun x hx => hc x (Finset.mem_insert_of_mem hx)) hsum
    intro o ho
    rcases Finset.mem_insert.mp ho with h | h
    · rw [h]; exact hca
    · exact hrest o h

section Main

variable {r : ℕ}

/-- On the base point a coordinate with a smaller position is at least as high. -/
theorem basePtR_anti {N k B : ℕ} (hB : 1 ≤ B) (π : Equiv.Perm (Fin N)) {i j : Fin N}
    (h : ((π i : Fin N) : ℕ) < ((π j : Fin N) : ℕ)) : basePtR k B π j ≤ basePtR k B π i := by
  unfold basePtR basePt
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  split_ifs with h1 h2 h2
  · exact le_rfl
  · omega
  · push_cast
    exact neg_nonpos.mpr (pow_nonneg (by linarith) _)
  · push_cast
    exact neg_le_neg (pow_le_pow_right hB' h.le)

/-- On the base point `σ(y_i - y_j)` is `y_i - y_j` exactly when `i` is above `j`. -/
theorem relu_basePtR {N k B : ℕ} (hB : 1 ≤ B) (π : Equiv.Perm (Fin N)) {i j : Fin N}
    (hij : i ≠ j) :
    relu (basePtR k B π i - basePtR k B π j) =
      if π i < π j then basePtR k B π i - basePtR k B π j else 0 := by
  unfold relu
  have hne : ((π i : Fin N) : ℕ) ≠ ((π j : Fin N) : ℕ) := fun h =>
    hij (π.injective (Fin.ext h))
  split_ifs with h
  · have := basePtR_anti (k := k) hB π (Fin.lt_iff_val_lt_val.mp h)
    exact max_eq_right (by linarith)
  · have h' : ((π j : Fin N) : ℕ) < ((π i : Fin N) : ℕ) := by
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd (Fin.lt_iff_val_lt_val.mpr h') h
      · exact h'
    have := basePtR_anti (k := k) hB π h'
    exact max_eq_left (by linarith)

end Main

/-! ## Tie sets and fibers -/

open scoped Nat

theorem subtypeCongr_apply_pos {α : Type*} {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x })
    {a : α} (h : p a) : Equiv.subtypeCongr e f a = e ⟨a, h⟩ := by
  simp [Equiv.subtypeCongr, h]

theorem subtypeCongr_apply_neg {α : Type*} {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x })
    {a : α} (h : ¬p a) : Equiv.subtypeCongr e f a = f ⟨a, h⟩ := by
  simp [Equiv.subtypeCongr, h]

theorem card_fiber_eq {N k : ℕ} {T T' : Finset (Fin N)} (h : T.card = T'.card) :
    (fiber k T).card = (fiber k T').card := by
  classical
  have hc : Fintype.card {x // x ∈ T'} = Fintype.card {x // x ∈ T} := by simp [h]
  have hc' : Fintype.card {x // ¬ x ∈ T'} = Fintype.card {x // ¬ x ∈ T} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hc]
  let σ : Equiv.Perm (Fin N) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq hc) (Fintype.equivOfCardEq hc')
  have hσ : ∀ x, x ∈ T' ↔ σ x ∈ T := by
    intro x
    by_cases hx : x ∈ T'
    · have e1 : σ x = _ :=
        subtypeCongr_apply_pos (p := fun y => y ∈ T') (q := fun y => y ∈ T) _ _ hx
      rw [e1]
      simp only [hx, true_iff]
      exact ((Fintype.equivOfCardEq hc) ⟨x, hx⟩).2
    · have e1 : σ x = _ :=
        subtypeCongr_apply_neg (p := fun y => y ∈ T') (q := fun y => y ∈ T) _ _ hx
      rw [e1]
      simp only [hx, false_iff]
      exact ((Fintype.equivOfCardEq hc') ⟨x, hx⟩).2
  refine card_congr (fun π _ => π * σ) ?_ ?_ ?_
  · intro π hπ
    simp only [fiber, mem_filter, mem_univ, true_and] at hπ ⊢
    ext x
    simp [mem_tieSet, hσ x, ← hπ]
  · intro a b _ _ hab
    exact mul_right_cancel hab
  · intro π hπ
    refine ⟨π * σ⁻¹, ?_, by simp⟩
    simp only [fiber, mem_filter, mem_univ, true_and] at hπ ⊢
    ext x
    have := hσ (σ⁻¹ x)
    simp only [Equiv.Perm.apply_inv_self] at this
    simp [mem_tieSet, ← this, ← hπ]

theorem card_fiber {N k : ℕ} {T : Finset (Fin N)} (hT : T.card = k) :
    (fiber k T).card = k ! * (N - k)! := by
  classical
  have hkN : k ≤ N := by
    have := card_le_univ T
    rw [Fintype.card_fin, hT] at this
    exact this
  have hsum : (univ : Finset (Equiv.Perm (Fin N))).card =
      ∑ T' in powersetCard k (univ : Finset (Fin N)), (fiber k T').card := by
    rw [card_eq_sum_card_fiberwise (f := tieSet k) (t := powersetCard k univ)]
    · rfl
    · intro π _
      simp [mem_powersetCard, card_tieSet hkN]
  have hall : ∀ T' ∈ powersetCard k (univ : Finset (Fin N)),
      (fiber k T').card = (fiber k T).card := by
    intro T' hT'
    rw [mem_powersetCard] at hT'
    exact card_fiber_eq (hT'.2.trans hT.symm)
  rw [sum_congr rfl hall, sum_const, card_powersetCard, card_univ, Fintype.card_perm,
    card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hpos : 0 < N.choose k := Nat.choose_pos hkN
  have := Nat.choose_mul_factorial_mul_factorial hkN
  rw [mul_assoc] at this
  exact (Nat.eq_of_mul_eq_mul_left hpos (this.trans hsum)).symm

/-! ## Orders with prescribed pairs -/

theorem tieSet_mul_swap {N k : ℕ} {π : Equiv.Perm (Fin N)} {a b : Fin N}
    (ha : a ∉ tieSet k π) (hb : b ∉ tieSet k π) :
    tieSet k (π * Equiv.swap a b) = tieSet k π := by
  ext x
  rw [mem_tieSet, mem_tieSet, Equiv.Perm.mul_apply]
  rw [mem_tieSet] at ha hb
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left]
    exact iff_of_false hb ha
  by_cases hxb : x = b
  · subst hxb
    rw [Equiv.swap_apply_right]
    exact iff_of_false ha hb
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

open Classical in
theorem card_fiber_pairsOrdered {N k : ℕ} {T : Finset (Fin N)} (hT : T.card = k)
    (P : Finset (Fin N × Fin N)) (hne : ∀ p ∈ P, p.1 ≠ p.2)
    (hdisj : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
      p.1 ≠ p'.1 ∧ p.1 ≠ p'.2 ∧ p.2 ≠ p'.1 ∧ p.2 ≠ p'.2)
    (hout : ∀ p ∈ P, p.1 ∉ T ∧ p.2 ∉ T) :
    ((fiber k T).filter fun π => ∀ p ∈ P, π p.1 < π p.2).card * 2 ^ P.card =
      k ! * (N - k)! := by
  revert hne hdisj hout
  induction P using Finset.induction_on with
  | empty =>
    intro _ _ _
    simp only [not_mem_empty, IsEmpty.forall_iff, implies_true, filter_True, card_empty,
      pow_zero, mul_one]
    exact card_fiber hT
  | @insert p P hp ih =>
    intro hne hdisj hout
    have hne' : ∀ q ∈ P, q.1 ≠ q.2 := fun q hq => hne q (mem_insert_of_mem hq)
    have hdisj' : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' →
        q.1 ≠ q'.1 ∧ q.1 ≠ q'.2 ∧ q.2 ≠ q'.1 ∧ q.2 ≠ q'.2 :=
      fun q hq q' hq' => hdisj q (mem_insert_of_mem hq) q' (mem_insert_of_mem hq')
    have hout' : ∀ q ∈ P, q.1 ∉ T ∧ q.2 ∉ T := fun q hq => hout q (mem_insert_of_mem hq)
    have IH := ih hne' hdisj' hout'
    set S := (fiber k T).filter fun π => ∀ q ∈ P, π q.1 < π q.2 with hS
    have hS' : ((fiber k T).filter fun π => ∀ q ∈ insert p P, π q.1 < π q.2) =
        S.filter fun π => π p.1 < π p.2 := by
      ext π
      simp only [hS, mem_filter, forall_mem_insert]
      tauto
    have hp1 := (hout p (mem_insert_self p P)).1
    have hp2 := (hout p (mem_insert_self p P)).2
    have hpne := hne p (mem_insert_self p P)
    -- the involution `π ↦ π * swap p.1 p.2` preserves `S`
    have hmapS : ∀ π ∈ S, π * Equiv.swap p.1 p.2 ∈ S := by
      intro π hπ
      simp only [hS, fiber, mem_filter, mem_univ, true_and] at hπ ⊢
      refine ⟨?_, ?_⟩
      · rw [tieSet_mul_swap (hπ.1 ▸ hp1) (hπ.1 ▸ hp2), hπ.1]
      · intro q hq
        have hqp : p ≠ q := fun h => hp (h ▸ hq)
        obtain ⟨h1, h2, h3, h4⟩ := hdisj p (mem_insert_self p P) q (mem_insert_of_mem hq) hqp
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h3),
          Equiv.swap_apply_of_ne_of_ne (Ne.symm h2) (Ne.symm h4)]
        exact hπ.2 q hq
    have hhalf : (S.filter fun π => π p.1 < π p.2).card =
        (S.filter fun π => ¬ π p.1 < π p.2).card := by
      refine card_congr (fun π _ => π * Equiv.swap p.1 p.2) ?_ ?_ ?_
      · intro π hπ
        rw [mem_filter] at hπ ⊢
        refine ⟨hmapS π hπ.1, ?_⟩
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
        exact not_lt.mpr hπ.2.le
      · intro a b _ _ hab
        exact mul_right_cancel hab
      · intro π hπ
        rw [mem_filter] at hπ
        refine ⟨π * Equiv.swap p.1 p.2, ?_, ?_⟩
        · rw [mem_filter]
          refine ⟨hmapS π hπ.1, ?_⟩
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
            Equiv.swap_apply_right]
          have : π p.1 ≠ π p.2 := fun h => hpne (π.injective h)
          exact lt_of_le_of_ne (not_lt.mp hπ.2) (Ne.symm this)
        · show π * Equiv.swap p.1 p.2 * Equiv.swap p.1 p.2 = π
          rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    have hsplit := filter_card_add_filter_neg_card_eq_card (s := S) (fun π => π p.1 < π p.2)
    rw [← hhalf] at hsplit
    rw [hS', card_insert_of_not_mem hp, pow_succ, ← IH, ← hsplit]
    ring

end MaxCaterpillar.Count
