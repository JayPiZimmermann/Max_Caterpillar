import MaxCaterpillar.CountExp.Defs

/-!
# Step 2 (a): the digit argument

At the base point of a locality the preactivation of a normalized key is
`-∑_{o ∉ T} c_o B^{π o}` with integer digits `c_o = κ_o - #{neighbours above o}`
and `|c_o| < B`; it vanishes only when every digit vanishes, which is condition (a).
-/

open BigOperators Finset

namespace MaxCaterpillar.CountExp

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain CountCubic

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

open Classical in
/-- A sum over the pairs `M` as a double sum over the coordinates. -/
theorem sum_pairSet_eq {key : RealKey (r + 1)} (hkey : key ∈ normalizedKeys r)
    (g : Fin (r + 1 + 1) → Fin (r + 1 + 1) → ℝ) :
    ∑ p in pairSet key, g p.1 p.2 =
      ∑ i, ∑ j, if HasPair key i j then g i j else 0 := by
  classical
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨hasPair_lt hkey h, h⟩⟩

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

theorem balanced_of_realUnitArg_eq_zero {r k B : ℕ} {key : RealKey (r + 1)}
    (hkey : key ∈ normalizedKeys r)
    (hB : ∑ o, |keyHead key o| + ((pairSet key).card : ℝ) < B)
    (π : Equiv.Perm (Fin (r + 1 + 1)))
    (h : realUnitArg key (basePtR k B π) = 0) :
    Balanced (HingeNbr key) (kappa key) k π := by
  classical
  have hsumh : 0 ≤ ∑ o, |keyHead key o| := Finset.sum_nonneg (fun o _ => abs_nonneg _)
  have hBpos : (0 : ℝ) < B := by
    have : (0 : ℝ) ≤ ((pairSet key).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hBpos)
  choose hz hhz using keyHead_isInt hkey
  -- the indicator of "`(i, j)` is a pair and `i` is above `j`"
  obtain ⟨ai, hai⟩ : ∃ ai : Fin (r + 1 + 1) → Fin (r + 1 + 1) → ℤ,
      ∀ i j, ai i j = if HasPair key i j ∧ π i < π j then 1 else 0 := ⟨_, fun _ _ => rfl⟩
  -- the digits `c_o = h_o + #{pairs (o, x), o above x} - #{pairs (x, o), x above o}`
  obtain ⟨z, hz_def⟩ : ∃ z : Fin (r + 1 + 1) → ℤ,
      ∀ o, z o = hz o + ∑ x, (ai o x - ai x o) := ⟨_, fun _ => rfl⟩
  have hnoself : ∀ o, ¬ HasPair key o o := fun o h => lt_irrefl o (hasPair_lt hkey h)
  -- Step A: the preactivation is `∑ₒ c_o y_o`
  have hpair : ∀ i j, (if HasPair key i j then
      relu (basePtR k B π i - basePtR k B π j) else 0) =
        (ai i j : ℝ) * basePtR k B π i - (ai i j : ℝ) * basePtR k B π j := by
    intro i j
    rw [hai]
    by_cases hp : HasPair key i j
    · rw [if_pos hp, relu_basePtR hB1 π (ne_of_lt (hasPair_lt hkey hp))]
      by_cases hl : π i < π j
      · simp [hp, hl]
      · simp [hp, hl]
    · simp [hp]
  have hA : realUnitArg key (basePtR k B π) = ∑ o, (z o : ℝ) * basePtR k B π o := by
    rw [realUnitArg_eq hkey, show ∑ p in pairSet key, relu (basePtR k B π p.1 - basePtR k B π p.2)
      = _ from sum_pairSet_eq hkey (fun i j => relu (basePtR k B π i - basePtR k B π j))]
    simp only [hpair]
    have hswap : ∑ i, ∑ j, (ai i j : ℝ) * basePtR k B π j =
        ∑ o, ∑ x, (ai x o : ℝ) * basePtR k B π o := Finset.sum_comm
    simp only [Finset.sum_sub_distrib, hswap, hz_def, hhz]
    push_cast
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
  -- Step B: the integer identity `∑_{o ∉ T} c_o B^{π o} = 0`
  have hZ : ∑ o, z o * basePt k B π o = 0 := by
    have : ((∑ o, z o * basePt k B π o : ℤ) : ℝ) = 0 := by
      push_cast; rw [← h, hA]; rfl
    exact_mod_cast this
  have hS : ∑ o in univ.filter (fun o => k ≤ ((π o : Fin (r + 1 + 1)) : ℕ)),
      z o * (B : ℤ) ^ ((π o : Fin (r + 1 + 1)) : ℕ) = 0 := by
    have : ∑ o, z o * basePt k B π o = -∑ o in univ.filter (fun o => k ≤ ((π o : Fin (r + 1 + 1)) : ℕ)),
        z o * (B : ℤ) ^ ((π o : Fin (r + 1 + 1)) : ℕ) := by
      rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro o _
      unfold basePt
      split_ifs with h1 h2 h2 <;> first | omega | ring
    linarith
  -- Step C: the digits are bounded by `B - 1`
  have hdeg : ∀ o, ∑ x, |(ai o x : ℝ) - ai x o| ≤ (pairSet key).card := by
    intro o
    have h1 : ((pairSet key).card : ℝ) = ∑ i, ∑ j, if HasPair key i j then (1 : ℝ) else 0 := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact sum_pairSet_eq hkey (fun _ _ => (1 : ℝ))
    have h2 : ∀ x, |(ai o x : ℝ) - ai x o| ≤
        (if HasPair key o x then (1 : ℝ) else 0) + (if HasPair key x o then 1 else 0) := by
      intro x
      rw [hai, hai]
      by_cases hp1 : HasPair key o x <;> by_cases hp2 : HasPair key x o <;>
        by_cases hl1 : π o < π x <;> by_cases hl2 : π x < π o <;> simp [hp1, hp2, hl1, hl2]
    have e1 : ∑ x, (if HasPair key o x then (1 : ℝ) else 0) =
        ∑ i, ∑ j, if i = o then (if HasPair key i j then (1 : ℝ) else 0) else 0 := by
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq']
    have e2 : ∑ x, (if HasPair key x o then (1 : ℝ) else 0) =
        ∑ i, ∑ j, if j = o then (if HasPair key i j then (1 : ℝ) else 0) else 0 := by
      simp [Finset.sum_ite_eq']
    calc ∑ x, |(ai o x : ℝ) - ai x o|
        ≤ ∑ x, ((if HasPair key o x then (1 : ℝ) else 0) + (if HasPair key x o then 1 else 0)) :=
          Finset.sum_le_sum fun x _ => h2 x
      _ = ∑ i, ∑ j, ((if i = o then (if HasPair key i j then (1 : ℝ) else 0) else 0) +
            (if j = o then (if HasPair key i j then (1 : ℝ) else 0) else 0)) := by
          rw [Finset.sum_add_distrib, e1, e2, ← Finset.sum_add_distrib]
          simp only [Finset.sum_add_distrib]
      _ ≤ ∑ i, ∑ j, if HasPair key i j then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          by_cases hp : HasPair key i j
          · have hij := hasPair_lt hkey hp
            by_cases hi : i = o
            · have hj : j ≠ o := fun hj => by subst hi; subst hj; exact lt_irrefl _ hij
              simp [hp, hi, hj]
            · simp only [hp, hi, if_true, if_false, zero_add]
              split_ifs <;> norm_num
          · simp [hp]
      _ = (pairSet key).card := h1.symm
  have hbound : ∀ o, |z o| < (B : ℤ) := by
    intro o
    have hr : |((z o : ℤ) : ℝ)| < B := by
      rw [hz_def]
      push_cast
      calc |(hz o : ℝ) + ∑ x, ((ai o x : ℝ) - ai x o)|
          ≤ |(hz o : ℝ)| + ∑ x, |(ai o x : ℝ) - ai x o| :=
            (abs_add _ _).trans (add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _)
        _ ≤ ∑ o', |keyHead key o'| + (pairSet key).card := by
            apply add_le_add
            · rw [← hhz]
              exact Finset.single_le_sum (f := fun o' => |keyHead key o'|)
                (fun _ _ => abs_nonneg _) (Finset.mem_univ o)
            · exact hdeg o
        _ < B := hB
    have : ((|z o| : ℤ) : ℝ) < ((B : ℤ) : ℝ) := by push_cast; exact hr
    exact_mod_cast this
  -- Step D: every digit vanishes, which is condition (a)
  intro o ho
  have hinj : Set.InjOn (fun o : Fin (r + 1 + 1) => ((π o : Fin (r + 1 + 1)) : ℕ))
      ↑(univ.filter (fun o => k ≤ ((π o : Fin (r + 1 + 1)) : ℕ))) :=
    fun a _ b _ hab => π.injective (Fin.ext hab)
  have hz0 : z o = 0 :=
    digits_eq_zero (B := (B : ℤ)) (by exact_mod_cast hB1) _ z _ hinj (fun o _ => hbound o) hS o
      (by simp [ho])
  have hk : kappa key o - upCount (HingeNbr key) π o = (z o : ℝ) := by
    unfold kappa upCount upNbrs
    rw [Finset.natCast_card_filter, Finset.natCast_card_filter, hz_def]
    push_cast
    rw [hhz]
    rw [add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [hai, hai]
    unfold HingeNbr
    by_cases hxo : x = o
    · subst hxo
      simp [hnoself]
    · have hπ : π x ≠ π o := fun h => hxo (π.injective h)
      by_cases hp1 : HasPair key o x
      · have hox := hasPair_lt hkey hp1
        have hp2 : ¬ HasPair key x o := fun h => absurd (hasPair_lt hkey h) (not_lt.mpr hox.le)
        rcases lt_or_gt_of_ne hπ with hl | hl
        · simp [hp1, hp2, hox, hl, hl.not_lt]
        · simp [hp1, hp2, hox, hl, hl.not_lt]
      · by_cases hp2 : HasPair key x o
        · simp [hp1, hp2]
        · simp [hp1, hp2]
  have : (z o : ℝ) = 0 := by exact_mod_cast hz0
  linarith

end Main

end MaxCaterpillar.CountExp

