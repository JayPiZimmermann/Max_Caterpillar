import MaxCaterpillar.Trees.Hubs

/-!
# The hub class: assembly and an exponential corollary

`HubOK D Δ`: every hinge neighbour of a vertex of hinge degree `> Δ` has `κ ≤ 0`.
It contains the trees of maximum hinge degree `≤ Δ` (no hubs) and the rooted stars
of Brunck et al. (their leaves have `κ = 0`).

* `choose_le_of_hubs`: `C(N, k) ≤ 2 (k+1) (6(2Δ-1))^k S |K|`, `S = Σ_{i ≤ 2k/(Δ+1)} C(N, i)`.
* `tree_hub_choose_le`: the same for tree face functions.
* `tree_hub_exponential`: for `Δ ≥ 3`, `3 ≤ k` and `(144 (2Δ-1)^2 + 1) k ≤ N`,
  `2^k ≤ 2 (k+1)^2 |K|`; with `k = ⌊N/(144(2Δ-1)^2+1)⌋` this is exponential in `N`.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

open MaxNN CountLower CountExp

/-- **Binomial count for the hub class (descriptions).** -/
theorem choose_le_of_hubs (r : ℕ) {ι : Type*} (K : Finset ι) (D : ι → Descr (r + 1 + 1))
    {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hlt : ∀ i ∈ K, ∀ m ∈ (D i).M, m.1 < m.2) (hleaf : ∀ i ∈ K, LeafProp (D i).M)
    (hH : ∀ i ∈ K, HubOK (D i) Δ)
    (child : ι → Fin (r + 1 + 1) × Fin (r + 1 + 1) → Fin (r + 1 + 1))
    (hchild : ∀ i ∈ K, ∀ m ∈ (D i).M, child i m = m.1 ∨ child i m = m.2)
    (hcinj : ∀ i ∈ K, Set.InjOn (child i) (D i).M)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ i in K, d i * (D i).unit x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    ((r + 1 + 1).choose k : ℝ) ≤ 2 * (k + 1) * (6 * (2 * Δ - 1 : ℕ)) ^ k *
      (∑ i in range (2 * k / (Δ + 1) + 1), ((r + 1 + 1).choose i : ℝ)) * K.card := by
  classical
  set C := 2 * (k + 1) * (6 * (2 * Δ - 1 : ℕ)) ^ k *
      (∑ i in range (2 * k / (Δ + 1) + 1), ((r + 1 + 1).choose i : ℝ)) with hC
  have hcover : (univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))) ⊆
      K.biUnion fun i => univ.filter (DPasses (D i) k) := by
    intro π _
    obtain ⟨i, hi, hp⟩ := exists_dpasses r K D hlt d a h hk hkN π
    exact mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨mem_univ _, hp⟩⟩
  have h1 := card_le_of_subset hcover
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  have h2 : ((r + 1 + 1)! : ℝ) ≤
      ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ) := by
    have := h1.trans card_biUnion_le
    exact_mod_cast this
  have h3 : ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ) ≤
      K.card * (C * (k ! * (r + 1 + 1 - k)! : ℕ)) := by
    calc ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ)
        ≤ ∑ _i in K, (C * (k ! * (r + 1 + 1 - k)! : ℕ) : ℝ) :=
          sum_le_sum fun i hi =>
            card_passes_le_hub (D i) (hlt i hi) (hleaf i hi) hΔ (hH i hi) (child i)
              (hchild i hi) (hcinj i hi) hkN
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hfac : ((r + 1 + 1)! : ℝ) = ((r + 1 + 1).choose k : ℝ) * (k ! * (r + 1 + 1 - k)! : ℕ) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkN]
    push_cast
    ring
  have hpos : (0 : ℝ) < (k ! * (r + 1 + 1 - k)! : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h4 := h2.trans h3
  rw [hfac] at h4
  have h5 : ((r + 1 + 1).choose k : ℝ) * (k ! * (r + 1 + 1 - k)! : ℕ) ≤
      (C * K.card) * (k ! * (r + 1 + 1 - k)! : ℕ) := by
    linarith
  exact le_of_mul_le_mul_right h5 hpos

/-! ## Tree faces -/

namespace TreeFace

variable {N : ℕ} (F : TreeFace N)

/-- The child endpoint of a tree edge. -/
noncomputable def child (m : Fin N × Fin N) : Fin N := by
  classical
  exact if m.1 ∈ F.edgeVerts ∧ F.parent m.1 = m.2 then m.1 else m.2

theorem normPair_gen_cases (v : Fin N) :
    normPair (F.gen v) = (v, F.parent v) ∨ normPair (F.gen v) = (F.parent v, v) := by
  unfold normPair gen
  split_ifs <;> simp

theorem child_normPair {v : Fin N} (hv : v ∈ F.edgeVerts) : F.child (normPair (F.gen v)) = v := by
  classical
  unfold child
  rcases F.normPair_gen_cases v with h | h <;> rw [h]
  · simp [hv]
  · rw [if_neg]
    rintro ⟨hp, hpp⟩
    have hv' := (F.mem_edgeVerts).mp hv
    have hp' := (F.mem_edgeVerts).mp hp
    have d1 := F.depth_lt v hv'.2 hv'.1
    have d2 := F.depth_lt (F.parent v) hp'.2 hp'.1
    rw [hpp] at d2
    omega

theorem descr_child_spec : ∀ m ∈ F.descr.M, F.child m = m.1 ∨ F.child m = m.2 := by
  intro m _
  unfold child
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem descr_child_inj : Set.InjOn F.child F.descr.M := by
  intro m hm m' hm' he
  obtain ⟨v, hv, rfl⟩ := mem_image.mp (mem_coe.mp hm)
  obtain ⟨v', hv', rfl⟩ := mem_image.mp (mem_coe.mp hm')
  rw [F.child_normPair (mem_filter.mp hv).1, F.child_normPair (mem_filter.mp hv').1] at he
  rw [he]

/-- A tree whose hinge degree is at most `Δ` everywhere is in the hub class. -/
theorem hubOK_of_hingeDeg_le {Δ : ℕ} (h : ∀ u, F.hingeDeg u ≤ Δ) : HubOK F.descr Δ := by
  intro v hv
  exact absurd ((F.incid_descr_le v).trans (h v)) (not_le.mpr hv)

end TreeFace

/-! ## Public statements -/

/-- **Binomial count for the hub class of trees.** If every unit `F` of a tree expansion of
`max_N` (`N = r + 2`) satisfies `HubOK F.descr Δ` (every hinge neighbour of a vertex of
hinge degree `> Δ` has `κ ≤ 0`), then for `3 ≤ k ≤ N`,
`C(N, k) ≤ 2 (k+1) (6(2Δ-1))^k (Σ_{i ≤ 2k/(Δ+1)} C(N, i)) |K|`. -/
theorem tree_hub_choose_le (r : ℕ) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) {Δ : ℕ} (hΔ : 1 ≤ Δ) (hH : ∀ F ∈ K, HubOK F.descr Δ)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    ((r + 1 + 1).choose k : ℝ) ≤ 2 * (k + 1) * (6 * (2 * Δ - 1 : ℕ)) ^ k *
      (∑ i in range (2 * k / (Δ + 1) + 1), ((r + 1 + 1).choose i : ℝ)) * K.card := by
  obtain ⟨d, a, h⟩ := hK
  have h' : ∀ x, Maximum (r + 1 + 1) x = ∑ F in K, d F * F.descr.unit x + auxiliary a x := by
    intro x
    rw [h x]
    congr 1
    exact sum_congr rfl fun F _ => by rw [TreeFace.descr_unit]
  exact choose_le_of_hubs r K (fun F => F.descr) hΔ (fun F _ => F.descr_lt)
    (fun F _ => F.descr_leaf) hH (fun F => F.child) (fun F _ => F.descr_child_spec)
    (fun F _ => F.descr_child_inj) d a h' hk hkN

/-- `(m - 1) C(N, j) ≤ C(N, j + 1)` when `j < k` and `m k ≤ N`. -/
theorem choose_step {N k m j : ℕ} (hj : j < k) (hmk : m * k ≤ N) (hm : 1 ≤ m) :
    (m - 1) * N.choose j ≤ N.choose (j + 1) := by
  have e := Nat.choose_succ_right_eq N j
  have e1 : (m - 1) * k = m * k - k := by rw [tsub_mul, one_mul]
  have e2 : k ≤ m * k := Nat.le_mul_of_pos_left (by omega)
  have e3 : (m - 1) * (j + 1) ≤ (m - 1) * k := Nat.mul_le_mul_left _ hj
  have h1 : (m - 1) * (j + 1) ≤ N - j := by
    generalize (m - 1) * (j + 1) = Y at *
    generalize (m - 1) * k = X at *
    generalize m * k = Z at *
    omega
  have h3 : (m - 1) * N.choose j * (j + 1) ≤ N.choose (j + 1) * (j + 1) := by
    calc (m - 1) * N.choose j * (j + 1) = N.choose j * ((m - 1) * (j + 1)) := by ring
      _ ≤ N.choose j * (N - j) := Nat.mul_le_mul_left _ h1
      _ = N.choose (j + 1) * (j + 1) := e.symm
  exact le_of_mul_le_mul_right h3 (Nat.succ_pos j)

theorem choose_pow_le {N k m : ℕ} (hmk : m * k ≤ N) (hm : 1 ≤ m) :
    ∀ t i, i + t ≤ k → (m - 1) ^ t * N.choose i ≤ N.choose (i + t) := by
  intro t
  induction t with
  | zero => intro i _; simp
  | succ t ih =>
    intro i hit
    have h1 := ih i (by omega)
    have h2 := choose_step (N := N) (k := k) (m := m) (j := i + t) (by omega) hmk hm
    calc (m - 1) ^ (t + 1) * N.choose i = (m - 1) * ((m - 1) ^ t * N.choose i) := by ring
      _ ≤ (m - 1) * N.choose (i + t) := Nat.mul_le_mul_left _ h1
      _ ≤ N.choose (i + t + 1) := h2

/-- **Exponential count for the hub class of trees.** For `Δ ≥ 3`, `A = 2Δ - 1`,
`3 ≤ k` and `(144 A² + 1) k ≤ N`: `2^k ≤ 2 (k+1)^2 |K|`. -/
theorem tree_hub_exponential (r : ℕ) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) {Δ : ℕ} (hΔ : 3 ≤ Δ) (hH : ∀ F ∈ K, HubOK F.descr Δ)
    {k : ℕ} (hk : 3 ≤ k) (hkN : (144 * (2 * Δ - 1) ^ 2 + 1) * k ≤ r + 1 + 1) :
    (2 : ℝ) ^ k ≤ 2 * (k + 1) ^ 2 * K.card := by
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * Δ - 1 := ⟨_, rfl⟩
  rw [← hA] at hkN
  have hA1 : 1 ≤ A := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = 144 * A ^ 2 + 1 := ⟨_, rfl⟩
  rw [← hm] at hkN
  have hm1 : 1 ≤ m := by omega
  have hkN' : k ≤ r + 1 + 1 := le_trans (Nat.le_mul_of_pos_left (by omega)) hkN
  have hmain := tree_hub_choose_le r hK (by omega : 1 ≤ Δ) hH hk hkN'
  rw [← hA] at hmain
  obtain ⟨q, hq⟩ : ∃ q, q = 2 * k / (Δ + 1) := ⟨_, rfl⟩
  rw [← hq] at hmain
  have hq2 : 2 * q ≤ k := by
    have h1 : q * (Δ + 1) ≤ 2 * k := by rw [hq]; exact Nat.div_mul_le_self _ _
    have h4 : 4 * q ≤ q * (Δ + 1) := by nlinarith
    linarith
  -- each term `C(N, i) (12A)^k ≤ C(N, k)` for `i ≤ q`
  have hterm : ∀ i ∈ range (q + 1), (((r + 1 + 1).choose i : ℝ)) * (12 * A : ℝ) ^ k ≤ (r + 1 + 1).choose k := by
    intro i hi
    have hi' : i ≤ q := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hik : i ≤ k := by omega
    have hp := choose_pow_le (N := r + 1 + 1) (k := k) hkN hm1 (k - i) i (by omega)
    rw [Nat.add_sub_cancel' hik] at hp
    have hpr : ((m - 1 : ℕ) : ℝ) ^ (k - i) * ((r + 1 + 1).choose i : ℝ) ≤ (r + 1 + 1).choose k := by exact_mod_cast hp
    have hm' : ((m - 1 : ℕ) : ℝ) = (12 * A : ℝ) ^ 2 := by
      rw [hm, Nat.add_sub_cancel]; push_cast; ring
    rw [hm', ← pow_mul] at hpr
    have h12 : (1 : ℝ) ≤ 12 * A := by
      have : (1 : ℝ) ≤ A := by exact_mod_cast hA1
      linarith
    have hle : (12 * A : ℝ) ^ k ≤ (12 * A : ℝ) ^ (2 * (k - i)) :=
      pow_le_pow_right h12 (by omega)
    calc ((r + 1 + 1).choose i : ℝ) * (12 * A : ℝ) ^ k ≤ ((r + 1 + 1).choose i : ℝ) * (12 * A : ℝ) ^ (2 * (k - i)) :=
          mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
      _ = (12 * A : ℝ) ^ (2 * (k - i)) * ((r + 1 + 1).choose i : ℝ) := by ring
      _ ≤ (r + 1 + 1).choose k := hpr
  have hS : (∑ i in range (q + 1), ((r + 1 + 1).choose i : ℝ)) * (12 * A : ℝ) ^ k ≤ (k + 1) * (r + 1 + 1).choose k := by
    rw [sum_mul]
    calc ∑ i in range (q + 1), ((r + 1 + 1).choose i : ℝ) * (12 * A : ℝ) ^ k
        ≤ ∑ _i in range (q + 1), ((r + 1 + 1).choose k : ℝ) := sum_le_sum hterm
      _ = (q + 1) * (r + 1 + 1).choose k := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ (k + 1) * (r + 1 + 1).choose k := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          have : (q : ℝ) ≤ k := by exact_mod_cast (show q ≤ k by omega)
          linarith
  have hCpos : (0 : ℝ) < (r + 1 + 1).choose k := by exact_mod_cast Nat.choose_pos hkN'
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA1
  -- combine
  have key : ((r + 1 + 1).choose k : ℝ) * (12 * A : ℝ) ^ k ≤
      ((r + 1 + 1).choose k : ℝ) * ((6 * A : ℝ) ^ k * (2 * (k + 1) ^ 2 * K.card)) := by
    have hmain' : ((r + 1 + 1).choose k : ℝ) ≤ 2 * (k + 1) * (6 * A : ℝ) ^ k *
        (∑ i in range (q + 1), ((r + 1 + 1).choose i : ℝ)) * K.card := by
      simpa using hmain
    have hK0 : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
    calc ((r + 1 + 1).choose k : ℝ) * (12 * A : ℝ) ^ k
        ≤ (2 * (k + 1) * (6 * A : ℝ) ^ k *
            (∑ i in range (q + 1), ((r + 1 + 1).choose i : ℝ)) * K.card) * (12 * A : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right hmain' (by positivity)
      _ = 2 * (k + 1) * (6 * A : ℝ) ^ k * K.card *
            ((∑ i in range (q + 1), ((r + 1 + 1).choose i : ℝ)) * (12 * A : ℝ) ^ k) := by ring
      _ ≤ 2 * (k + 1) * (6 * A : ℝ) ^ k * K.card * ((k + 1) * (r + 1 + 1).choose k) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = ((r + 1 + 1).choose k : ℝ) * ((6 * A : ℝ) ^ k * (2 * (k + 1) ^ 2 * K.card)) := by ring
  have key2 := le_of_mul_le_mul_left key hCpos
  have h12 : (12 * A : ℝ) ^ k = 2 ^ k * (6 * A : ℝ) ^ k := by rw [← mul_pow]; ring
  rw [h12] at key2
  have h6 : (0 : ℝ) < (6 * A : ℝ) ^ k := by positivity
  nlinarith

end MaxCaterpillar.Trees

/-! ## The rooted stars of Brunck et al. are in the hub class -/

namespace MaxCaterpillar.Trees

open MaxNN CountLower CountExp

/-- The rooted star with apex `a` and root `c` as a tree face: every other label is a leaf
of `c`, with the hinge `σ(y_c - y_l)`. -/
def starFace {N : ℕ} (a c : Fin N) (hac : c ≠ a) : TreeFace N where
  apex := a
  root := c
  parent := fun _ => c
  depth := fun v => if v = c then 0 else 1
  up := fun _ => true
  state := fun _ => .hinge
  root_ne_apex := hac
  parent_ne_apex := fun _ _ _ => hac
  depth_lt := fun v _ hvc => by simp [hvc]

theorem starFace_unit {N : ℕ} (a c : Fin N) (hac : c ≠ a) :
    (starFace a c hac).unit = rootedStar a c := by
  funext y
  unfold TreeFace.unit rootedStar TreeFace.edgeTerm TreeFace.edgeVerts TreeFace.gen
  rfl

theorem starFace_hubOK {N : ℕ} (a c : Fin N) (hac : c ≠ a) {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    HubOK (starFace a c hac).descr Δ := by
  classical
  set F := starFace a c hac
  have hgen : ∀ v, F.gen v = (c, v) := fun v => by simp [F, TreeFace.gen, starFace]
  have hM : ∀ m ∈ F.descr.M, ∃ v ∈ F.edgeVerts, m = TreeFace.normPair (c, v) := by
    intro m hm
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hm
    exact ⟨v, (mem_filter.mp hv).1, by rw [hgen]⟩
  have hev : ∀ v, v ∈ F.edgeVerts ↔ v ≠ c ∧ v ≠ a := fun v => F.mem_edgeVerts
  have hnp : ∀ v, TreeFace.normPair (c, v) = (c, v) ∨ TreeFace.normPair (c, v) = (v, c) := by
    intro v; unfold TreeFace.normPair; split_ifs <;> simp
  -- a vertex other than `c` has degree at most one
  have hdeg : ∀ v, v ≠ c → deg F.descr v ≤ 1 := by
    intro v hvc
    unfold deg incid
    have hsub : F.descr.M.filter (fun m => m.1 = v ∨ m.2 = v) ⊆ {TreeFace.normPair (c, v)} := by
      intro m hm
      obtain ⟨hmM, hmv⟩ := mem_filter.mp hm
      obtain ⟨w, hw, rfl⟩ := hM m hmM
      rw [mem_singleton]
      have hwv : w = v := by
        rcases hnp w with h | h <;> rw [h] at hmv <;> simp only at hmv <;>
          rcases hmv with h' | h'
        · exact absurd h'.symm hvc
        · exact h'
        · exact h'
        · exact absurd h'.symm hvc
      rw [hwv]
    exact (card_le_of_subset hsub).trans (card_singleton _).le
  -- `κ = 0` at every leaf
  have hkappa : ∀ u, u ∈ F.edgeVerts → DKappa F.descr u = 0 := by
    intro u hu
    have hu' := (hev u).mp hu
    unfold DKappa
    have hh : F.descr.h u = if u < c then -1 else 0 := by
      show ((if u = c then 1 else 0) - (if u = a then 1 else 0)) +
        ∑ v in F.edgeVerts, (if F.headShift v then
          ((if u = (F.gen v).1 then 1 else 0) - (if u = (F.gen v).2 then 1 else 0)) else 0) = _
      rw [if_neg hu'.1, if_neg hu'.2]
      simp only [hgen, zero_sub, sub_zero, zero_add]
      have hhs : ∀ v, F.headShift v ↔ v < c := by
        intro v
        unfold TreeFace.headShift
        rw [hgen v]
        have hs : F.state v = .hinge := rfl
        rw [hs]
        simp
      simp only [hhs, if_neg hu'.1, zero_sub]
      rw [Finset.sum_eq_single u]
      · split_ifs <;> simp_all
      · intro b _ hb
        split_ifs <;> simp_all
      · intro h; exact absurd hu h
    have hc : (F.descr.M.filter fun m => m.1 = u).card = if u < c then 1 else 0 := by
      have hset : F.descr.M.filter (fun m => m.1 = u) =
          if u < c then {TreeFace.normPair (c, u)} else ∅ := by
        ext m
        simp only [mem_filter]
        constructor
        · rintro ⟨hmM, hm1⟩
          obtain ⟨w, hw, rfl⟩ := hM m hmM
          have hwc : w ≠ c := ((hev w).mp hw).1
          by_cases hcw : c < w
          · have e : TreeFace.normPair (c, w) = (c, w) := if_pos hcw
            rw [e] at hm1
            exact absurd hm1.symm hu'.1
          · have e : TreeFace.normPair (c, w) = (w, c) := if_neg hcw
            rw [e] at hm1
            have hwu : w = u := hm1
            have hwlt : w < c := lt_of_le_of_ne (not_lt.mp hcw) hwc
            rw [if_pos (hwu ▸ hwlt), mem_singleton, hwu]
        · intro hm
          split_ifs at hm with h
          · rw [mem_singleton] at hm
            subst hm
            refine ⟨mem_image.mpr ⟨u, mem_filter.mpr ⟨hu, rfl⟩, by rw [hgen]⟩, ?_⟩
            unfold TreeFace.normPair
            simp [not_lt.mpr h.le]
          · exact absurd hm (not_mem_empty m)
      rw [hset]
      split_ifs <;> simp
    rw [hh, hc]
    split_ifs <;> norm_num
  intro v hv u hadj
  have hvc : v = c := by
    by_contra h
    have := hdeg v h
    omega
  subst hvc
  -- the neighbour is a leaf
  have hu : u ∈ F.edgeVerts := by
    rcases hadj with h | h
    · obtain ⟨w, hw, hm⟩ := hM _ h
      rcases hnp w with h' | h' <;> rw [h'] at hm <;> simp only [Prod.mk.injEq] at hm
      · rw [hm.2]; exact hw
      · exact absurd hm.1 ((hev w).mp hw).1.symm
    · obtain ⟨w, hw, hm⟩ := hM _ h
      rcases hnp w with h' | h' <;> rw [h'] at hm <;> simp only [Prod.mk.injEq] at hm
      · exact absurd hm.2 ((hev w).mp hw).1.symm
      · rw [hm.1]; exact hw
  rw [hkappa u hu]

/-- **The rooted stars with an arbitrary vocabulary of bounded-degree trees.** Every
expansion of `max_N` by tree face functions each of which is a rooted star or has hinge
degree `≤ Δ` (`Δ ≥ 3`) satisfies `2^k ≤ 2 (k+1)^2 |K|` whenever `3 ≤ k` and
`(144 (2Δ-1)^2 + 1) k ≤ N`. -/
theorem tree_star_or_bounded_exponential (r : ℕ) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) {Δ : ℕ} (hΔ : 3 ≤ Δ)
    (hcls : ∀ F ∈ K, (∃ a c, ∃ hac : c ≠ a, F = starFace a c hac) ∨ ∀ u, F.hingeDeg u ≤ Δ)
    {k : ℕ} (hk : 3 ≤ k) (hkN : (144 * (2 * Δ - 1) ^ 2 + 1) * k ≤ r + 1 + 1) :
    (2 : ℝ) ^ k ≤ 2 * (k + 1) ^ 2 * K.card := by
  refine tree_hub_exponential r hK hΔ (fun F hF => ?_) hk hkN
  rcases hcls F hF with ⟨a, c, hac, rfl⟩ | h
  · exact starFace_hubOK a c hac (by omega)
  · exact F.hubOK_of_hingeDeg_le h

end MaxCaterpillar.Trees
