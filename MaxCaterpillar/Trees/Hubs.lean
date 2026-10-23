import MaxCaterpillar.Trees.BoundedDegreeMain

/-!
# Hubs: an exponential count covering bounded degree and rooted stars

Fix `Δ ≥ 1`.  A *hub* of a unit is a vertex of hinge degree `> Δ`.  The class `HubOK Δ`:
every hinge neighbour `u` of a hub has `κ_u ≤ 0`.  Trees of maximum hinge degree `≤ Δ`
(no hubs) and the rooted stars of Brunck et al. (all leaves have `κ = 0`) are in the class.

Per unit (`A = 2Δ - 1`), with `T` the tie set of a passed locality:
* a tied hub has all its neighbours tied (an untied neighbour would need `κ ≥ 1`);
* a non-hub vertex all of whose neighbours are hubs is tied iff some neighbour hub is tied
  or `κ ≠ 0`; so `T` is determined by its hubs and by its vertices on edges between
  non-hubs (at most `2e'` vertices, `e'` such edges);
* `(Δ + 1) · #tied hubs ≤ 2k` (the edges inside `T` number at most `k`);
* a matching in the non-hub edges outside `T` (`A |P| ≥ e' - Δ k`) halves the orders.
Hence every unit passes at most `2 (k+1) (6A)^k S k! (N-k)!` localities of order `k`, where
`S = Σ_{i ≤ 2k/(Δ+1)} C(N, i)`, and `C(N, k) ≤ 2 (k+1) (6A)^k S |K|`.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

open MaxNN CountLower CountExp

section Hubs

open Classical

variable {N : ℕ}

/-- Prescribing a vertex-disjoint set of pairs outside `T` divides the balanced orders
by `2^|P0|`. -/
theorem card_balanced_fiber_of_matching (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2)
    (hleaf : LeafProp D.M) {k : ℕ} {T : Finset (Fin N)} (hT : T.card = k)
    (P0 : Finset (Fin N × Fin N)) (hP0sub : P0 ⊆ D.M) (hP0disj : VDisj P0)
    (hP0out : ∀ m ∈ P0, m.1 ∉ T ∧ m.2 ∉ T) :
    ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card * 2 ^ P0.card ≤
      k ! * (N - k)! := by
  by_cases hex : ∃ π₀, π₀ ∈ (fiber k T).filter (Balanced (DAdj D) (DKappa D) k)
  swap
  · rw [not_exists] at hex
    rw [card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr hex), zero_mul]
    exact Nat.zero_le _
  obtain ⟨π₀, hπ₀⟩ := hex
  simp only [fiber, mem_filter, mem_univ, true_and] at hπ₀
  obtain ⟨hπ₀T, hπ₀b⟩ := hπ₀
  let f : Fin N × Fin N → Fin N × Fin N := fun m => if π₀ m.1 < π₀ m.2 then m else (m.2, m.1)
  have hf : ∀ m, f m = m ∨ f m = (m.2, m.1) := fun m => by
    simp only [f]; split_ifs <;> simp
  have hP0M : ∀ m ∈ P0, m ∈ D.M := fun m hm => hP0sub hm
  have hinj : Set.InjOn f P0 := by
    intro m hm m' hm' he
    have l1 := hlt m (hP0M m (mem_coe.mp hm))
    have l2 := hlt m' (hP0M m' (mem_coe.mp hm'))
    rcases hf m with h1 | h1 <;> rcases hf m' with h2 | h2 <;> rw [h1, h2] at he
    · exact he
    · have e1 : m.1 = m'.2 := congrArg Prod.fst he
      have e2 : m.2 = m'.1 := congrArg Prod.snd he
      exfalso; rw [e1, e2] at l1; exact lt_asymm l1 l2
    · have e1 : m.2 = m'.1 := congrArg Prod.fst he
      have e2 : m.1 = m'.2 := congrArg Prod.snd he
      exfalso; rw [← e1, ← e2] at l2; exact lt_asymm l1 l2
    · have e1 : m.2 = m'.2 := congrArg Prod.fst he
      have e2 : m.1 = m'.1 := congrArg Prod.snd he
      exact Prod.ext e2 e1
  set P := P0.image f
  have hPcard : P.card = P0.card := card_image_of_injOn hinj
  have hne : ∀ p ∈ P, p.1 ≠ p.2 := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    have := ne_of_lt (hlt m (hP0M m hm))
    rcases hf m with h | h <;> rw [h]
    · exact this
    · exact this.symm
  have hdisj : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
      p.1 ≠ p'.1 ∧ p.1 ≠ p'.2 ∧ p.2 ≠ p'.1 ∧ p.2 ≠ p'.2 := by
    intro p hp p' hp' hpp'
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    obtain ⟨m', hm', rfl⟩ := mem_image.mp hp'
    have hmm' : m ≠ m' := fun h => hpp' (by rw [h])
    have := hP0disj m hm m' hm' hmm'
    rcases hf m with h | h <;> rcases hf m' with h' | h' <;> rw [h, h'] <;> (try dsimp only) <;>
      tauto
  have hout : ∀ p ∈ P, p.1 ∉ T ∧ p.2 ∉ T := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    have := hP0out m hm
    rcases hf m with h | h <;> rw [h]
    · exact this
    · exact ⟨this.2, this.1⟩
  have hcount := card_fiber_pairsOrdered hT P hne hdisj hout
  have hsubF : (fiber k T).filter (Balanced (DAdj D) (DKappa D) k) ⊆
      (fiber k T).filter fun π => ∀ p ∈ P, π p.1 < π p.2 := by
    intro π hπ
    simp only [fiber, mem_filter, mem_univ, true_and] at hπ ⊢
    obtain ⟨hπT, hπb⟩ := hπ
    refine ⟨hπT, ?_⟩
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    have hmO := hP0out m hm
    have hTeq : tieSet k π = tieSet k π₀ := hπT.trans hπ₀T.symm
    have hiff := orient_eq_of_balanced D hlt hleaf hTeq hπ₀b hπb (hP0M m hm)
      (by rw [hπ₀T]; exact hmO.1) (by rw [hπ₀T]; exact hmO.2)
    have hm12 : m.1 ≠ m.2 := ne_of_lt (hlt m (hP0M m hm))
    by_cases h : π₀ m.1 < π₀ m.2
    · rw [if_pos h]
      exact hiff.mp h
    · rw [if_neg h]
      show π m.2 < π m.1
      have hn : ¬ π m.1 < π m.2 := fun h' => h (hiff.mpr h')
      have hπne : π m.1 ≠ π m.2 := fun h' => hm12 (π.injective h')
      exact lt_of_le_of_ne (not_lt.mp hn) hπne.symm
  rw [← hPcard]
  calc ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card * 2 ^ P.card
      ≤ ((fiber k T).filter fun π => ∀ p ∈ P, π p.1 < π p.2).card * 2 ^ P.card :=
        Nat.mul_le_mul_right _ (card_le_of_subset hsubF)
    _ = k ! * (N - k)! := hcount

/-- The degree of `v` in the pairs of `D`. -/
noncomputable def deg (D : Descr N) (v : Fin N) : ℕ := (incid D.M v).card

/-- The class: every neighbour of a vertex of degree `> Δ` has `κ ≤ 0`. -/
def HubOK (D : Descr N) (Δ : ℕ) : Prop :=
  ∀ v, Δ < deg D v → ∀ u, DAdj D v u → DKappa D u ≤ 0

theorem dadj_symm {D : Descr N} {u v : Fin N} (h : DAdj D u v) : DAdj D v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- A tied hub has all its neighbours tied. -/
theorem nbr_mem_of_hub {D : Descr N} {Δ k : ℕ} {π : Equiv.Perm (Fin N)} (hH : HubOK D Δ)
    (hp : DPasses D k π) {v u : Fin N} (hv : v ∈ tieSet k π) (hvh : Δ < deg D v)
    (hadj : DAdj D v u) : u ∈ tieSet k π := by
  by_contra hu
  have huk : k ≤ ((π u : Fin N) : ℕ) := by
    by_contra h; exact hu (mem_tieSet'.mpr (by omega))
  have h1 := hp.1 u huk
  have h2 := hH v hvh u hadj
  have h3 : 1 ≤ upCount (DAdj D) π u := by
    unfold upCount
    apply card_pos.mpr
    exact ⟨v, mem_filter.mpr ⟨mem_univ _, dadj_symm hadj, upCount_lt_of_mem hv hu⟩⟩
  have : (1 : ℝ) ≤ upCount (DAdj D) π u := by exact_mod_cast h3
  linarith

/-- A non-hub vertex all of whose neighbours are hubs: tied iff a neighbour is tied or
`κ ≠ 0`. -/
theorem mem_tie_of_rest {D : Descr N} {Δ k : ℕ} {π : Equiv.Perm (Fin N)} (hH : HubOK D Δ)
    (hp : DPasses D k π) {u : Fin N} (hrest : ∀ x, DAdj D u x → Δ < deg D x) :
    u ∈ tieSet k π ↔ (∃ x, DAdj D u x ∧ x ∈ tieSet k π) ∨ DKappa D u ≠ 0 := by
  constructor
  · intro hu
    by_contra hcon
    push_neg at hcon
    exact hp.2 u (mem_tieSet'.mp hu) (fun x hx hadj => hcon.1 x hadj (mem_tieSet'.mpr hx))
      hcon.2
  · rintro (⟨x, hadj, hx⟩ | hκ)
    · exact nbr_mem_of_hub hH hp hx (hrest x hadj) (dadj_symm hadj)
    · by_contra hu
      have huk : k ≤ ((π u : Fin N) : ℕ) := by
        by_contra h; exact hu (mem_tieSet'.mpr (by omega))
      have h1 := hp.1 u huk
      have hle : DKappa D u ≤ 0 := by
        by_cases hx : ∃ x, DAdj D u x
        · obtain ⟨x, hx⟩ := hx
          exact hH x (hrest x hx) u (dadj_symm hx)
        · push_neg at hx
          have : upCount (DAdj D) π u = 0 := by
            unfold upCount
            rw [card_eq_zero, filter_eq_empty_iff]
            intro y _ hy
            exact hx y hy.1
          rw [this, Nat.cast_zero] at h1
          exact h1.symm.le
      have h0 : (0 : ℝ) ≤ upCount (DAdj D) π u := Nat.cast_nonneg _
      exact hκ (le_antisymm hle (h1 ▸ h0))

/-- The pairs between two non-hubs. -/
noncomputable def lightPairs (D : Descr N) (Δ : ℕ) : Finset (Fin N × Fin N) :=
  D.M.filter fun m => deg D m.1 ≤ Δ ∧ deg D m.2 ≤ Δ

/-- The endpoints of the light pairs. -/
noncomputable def lightVerts (D : Descr N) (Δ : ℕ) : Finset (Fin N) :=
  (lightPairs D Δ).image Prod.fst ∪ (lightPairs D Δ).image Prod.snd

/-- The hubs. -/
noncomputable def hubs (D : Descr N) (Δ : ℕ) : Finset (Fin N) := univ.filter fun v => Δ < deg D v

theorem card_lightVerts_le (D : Descr N) (Δ : ℕ) :
    (lightVerts D Δ).card ≤ 2 * (lightPairs D Δ).card := by
  unfold lightVerts
  calc _ ≤ ((lightPairs D Δ).image Prod.fst).card + ((lightPairs D Δ).image Prod.snd).card :=
        card_union_le _ _
    _ ≤ (lightPairs D Δ).card + (lightPairs D Δ).card := add_le_add card_image_le card_image_le
    _ = 2 * (lightPairs D Δ).card := by ring

/-- A vertex that is neither a hub nor on a light pair has only hub neighbours. -/
theorem rest_of_not_mem {D : Descr N} {Δ : ℕ} {u : Fin N} (hu1 : u ∉ hubs D Δ)
    (hu2 : u ∉ lightVerts D Δ) : ∀ x, DAdj D u x → Δ < deg D x := by
  intro x hx
  by_contra hxle
  push_neg at hxle
  have hu : deg D u ≤ Δ := by
    by_contra h; exact hu1 (mem_filter.mpr ⟨mem_univ _, not_le.mp h⟩)
  apply hu2
  unfold lightVerts lightPairs
  rcases hx with hx | hx
  · exact mem_union_left _ (mem_image.mpr ⟨(u, x), mem_filter.mpr ⟨hx, hu, hxle⟩, rfl⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨(x, u), mem_filter.mpr ⟨hx, hxle, hu⟩, rfl⟩)

/-- The number of tied hubs: `(Δ + 1) · #(T ∩ hubs) ≤ 2k`. -/
theorem card_tied_hubs (D : Descr N) {Δ k : ℕ} (hH : HubOK D Δ)
    (child : Fin N × Fin N → Fin N) (hchild : ∀ m ∈ D.M, child m = m.1 ∨ child m = m.2)
    (hcinj : Set.InjOn child D.M) {π : Equiv.Perm (Fin N)} (hp : DPasses D k π)
    (hk : k ≤ N) :
    (Δ + 1) * (tieSet k π ∩ hubs D Δ).card ≤ 2 * k := by
  set T := tieSet k π
  set H := T ∩ hubs D Δ
  set MT := D.M.filter fun m => m.1 ∈ T ∧ m.2 ∈ T
  have hMT : MT.card ≤ k := by
    rw [← card_tieSet hk π]
    apply card_le_card_of_inj_on child
    · intro m hm
      obtain ⟨hmM, h1, h2⟩ := mem_filter.mp hm
      rcases hchild m hmM with h | h <;> rw [h] <;> assumption
    · intro m hm m' hm' he
      exact hcinj (mem_filter.mp hm).1 (mem_filter.mp hm').1 he
  have hhub : ∀ v ∈ H, Δ + 1 ≤ deg D v := fun v hv =>
    (mem_filter.mp (mem_inter.mp hv).2).2
  have h1 : (Δ + 1) * H.card ≤ ∑ v in H, deg D v := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum hhub
  have h2 : ∑ v in H, deg D v = ∑ m in D.M, (H.filter fun v => m.1 = v ∨ m.2 = v).card := by
    unfold deg incid
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
  have h3 : ∀ m ∈ D.M, (H.filter fun v => m.1 = v ∨ m.2 = v).card ≤
      2 * (if m.1 ∈ T ∧ m.2 ∈ T then 1 else 0) := by
    intro m hm
    by_cases hin : ∃ v ∈ H, m.1 = v ∨ m.2 = v
    · obtain ⟨v, hvH, hv⟩ := hin
      have hvT := (mem_inter.mp hvH).1
      have hvh := hhub v hvH
      have hboth : m.1 ∈ T ∧ m.2 ∈ T := by
        rcases hv with rfl | rfl
        · exact ⟨hvT, nbr_mem_of_hub hH hp hvT hvh (Or.inl hm)⟩
        · exact ⟨nbr_mem_of_hub hH hp hvT hvh (Or.inr hm), hvT⟩
      rw [if_pos hboth, mul_one]
      have hsub : H.filter (fun v => m.1 = v ∨ m.2 = v) ⊆ {m.1, m.2} := by
        intro v hv
        rcases (mem_filter.mp hv).2 with rfl | rfl <;> simp
      exact (card_le_of_subset hsub).trans (card_insert_le _ _)
    · push_neg at hin
      have : H.filter (fun v => m.1 = v ∨ m.2 = v) = ∅ := by
        rw [filter_eq_empty_iff]
        intro v hv hc
        rcases hc with hc | hc
        · exact (hin v hv).1 hc
        · exact (hin v hv).2 hc
      rw [this, card_empty]
      exact Nat.zero_le _
  have h4 : ∑ m in D.M, 2 * (if m.1 ∈ T ∧ m.2 ∈ T then 1 else 0) = 2 * MT.card := by
    rw [← mul_sum, card_eq_sum_ones, sum_filter]
  calc (Δ + 1) * H.card ≤ ∑ v in H, deg D v := h1
    _ = _ := h2
    _ ≤ ∑ m in D.M, 2 * (if m.1 ∈ T ∧ m.2 ∈ T then 1 else 0) := sum_le_sum h3
    _ = 2 * MT.card := h4
    _ ≤ 2 * k := Nat.mul_le_mul_left _ hMT

/-- **Per-unit bound for the hub class.** -/
theorem card_passes_le_hub (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2) (hleaf : LeafProp D.M)
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hH : HubOK D Δ)
    (child : Fin N × Fin N → Fin N) (hchild : ∀ m ∈ D.M, child m = m.1 ∨ child m = m.2)
    (hcinj : Set.InjOn child D.M) {k : ℕ} (hk : k ≤ N) :
    (((univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k)).card : ℝ) ≤
      2 * (k + 1) * (6 * (2 * Δ - 1 : ℕ)) ^ k *
        (∑ i in range (2 * k / (Δ + 1) + 1), (N.choose i : ℝ)) * (k ! * (N - k)! : ℕ) := by
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * Δ - 1 := ⟨_, rfl⟩
  rw [← hA]
  have hA1 : 1 ≤ A := by omega
  have hΔA : Δ ≤ A := by omega
  set L := lightPairs D Δ
  set e := L.card
  set F := k ! * (N - k)!
  obtain ⟨pstar, hps⟩ : ∃ p, p = (e - Δ * k) / A := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = 2 * k / (Δ + 1) := ⟨_, rfl⟩
  rw [← hq]
  set Pass := (univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k)
  set 𝒯 := Pass.image (tieSet k)
  have hLM : L ⊆ D.M := filter_subset _ _
  have hdegL : ∀ o, (incid L o).card ≤ Δ := by
    intro o
    by_cases ho : deg D o ≤ Δ
    · exact (card_le_of_subset (filter_subset_filter _ hLM)).trans ho
    · have : incid L o = ∅ := by
        rw [incid, filter_eq_empty_iff]
        intro m hm hmo
        have hl := (mem_filter.mp hm).2
        rcases hmo with h | h
        · exact ho (h ▸ hl.1)
        · exact ho (h ▸ hl.2)
      rw [this, card_empty]; exact Nat.zero_le _
  have hcover : Pass ⊆ 𝒯.biUnion fun T => (fiber k T).filter (Balanced (DAdj D) (DKappa D) k) := by
    intro π hπ
    refine mem_biUnion.mpr ⟨tieSet k π, mem_image_of_mem _ hπ, ?_⟩
    simp only [fiber, mem_filter, mem_univ, true_and]
    exact (mem_filter.mp hπ).2.1
  have hper : ∀ T ∈ 𝒯, ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card * 2 ^ pstar ≤ F := by
    intro T hT
    obtain ⟨π, _, rfl⟩ := mem_image.mp hT
    have hTk : (tieSet k π).card = k := card_tieSet hk π
    set T := tieSet k π
    set EO := L.filter fun m => m.1 ∉ T ∧ m.2 ∉ T
    have hrest : L \ EO ⊆ T.biUnion (incid L) := by
      intro m hm
      rw [mem_sdiff, mem_filter] at hm
      push_neg at hm
      rw [mem_biUnion]
      by_cases h1 : m.1 ∈ T
      · exact ⟨m.1, h1, mem_filter.mpr ⟨hm.1, Or.inl rfl⟩⟩
      · exact ⟨m.2, hm.2 hm.1 h1, mem_filter.mpr ⟨hm.1, Or.inr rfl⟩⟩
    have hrestc : (L \ EO).card ≤ Δ * k := by
      calc (L \ EO).card ≤ (T.biUnion (incid L)).card := card_le_of_subset hrest
        _ ≤ ∑ t in T, (incid L t).card := card_biUnion_le
        _ ≤ ∑ _t in T, Δ := sum_le_sum fun t _ => hdegL t
        _ = Δ * k := by rw [sum_const, hTk, smul_eq_mul, mul_comm]
    have hdegO : ∀ o, (incid EO o).card ≤ Δ := fun o =>
      (card_le_of_subset (filter_subset_filter _ (filter_subset _ _))).trans (hdegL o)
    obtain ⟨P0, hP0sub, hP0disj, hP0card⟩ := exists_matching hΔ _ EO rfl hdegO
    rw [← hA] at hP0card
    have hEOsub : EO ⊆ L := filter_subset _ _
    have hc := card_balanced_fiber_of_matching D hlt hleaf hTk P0
      (hP0sub.trans (hEOsub.trans hLM)) hP0disj (fun m hm => (mem_filter.mp (hP0sub hm)).2)
    have hsplit := card_sdiff_add_card_eq_card hEOsub
    have hpp : pstar ≤ P0.card := by
      rw [hps]
      apply Nat.div_le_of_le_mul
      have : e - Δ * k ≤ A * P0.card := by
        have h1 : e ≤ A * P0.card + Δ * k := by
          have : EO.card ≤ A * P0.card := hP0card
          show L.card ≤ _
          linarith
        exact tsub_le_iff_right.mpr h1
      linarith [mul_comm A P0.card]
    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hpp)) hc
  -- counting the tie sets
  set Hs := (hubs D Δ).powerset.filter fun H => H.card ≤ q
  set Xs := (lightVerts D Δ).powerset.filter fun X => X.card ≤ k
  have hTcard : 𝒯.card ≤ Hs.card * Xs.card := by
    rw [← card_product]
    apply card_le_card_of_inj_on (fun T => (T ∩ hubs D Δ, T ∩ lightVerts D Δ))
    · intro T hT
      obtain ⟨π, hπ, rfl⟩ := mem_image.mp hT
      have hp := (mem_filter.mp hπ).2
      refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr (inter_subset_right _ _), ?_⟩,
        mem_filter.mpr ⟨mem_powerset.mpr (inter_subset_right _ _), ?_⟩⟩
      · rw [hq, Nat.le_div_iff_mul_le (by omega), mul_comm]
        exact card_tied_hubs D hH child hchild hcinj hp hk
      · exact (card_le_of_subset (inter_subset_left _ _)).trans (card_tieSet hk π).le
    · intro T hT T' hT' he
      obtain ⟨π, hπ, rfl⟩ := mem_image.mp hT
      obtain ⟨π', hπ', rfl⟩ := mem_image.mp hT'
      have hp := (mem_filter.mp hπ).2
      have hp' := (mem_filter.mp hπ').2
      simp only [Prod.mk.injEq] at he
      obtain ⟨eH, eL⟩ := he
      have hhub : ∀ y, y ∈ hubs D Δ → (y ∈ tieSet k π ↔ y ∈ tieSet k π') := by
        intro y hy
        constructor
        · intro h
          have : y ∈ tieSet k π ∩ hubs D Δ := mem_inter.mpr ⟨h, hy⟩
          rw [eH] at this; exact (mem_inter.mp this).1
        · intro h
          have : y ∈ tieSet k π' ∩ hubs D Δ := mem_inter.mpr ⟨h, hy⟩
          rw [← eH] at this; exact (mem_inter.mp this).1
      ext x
      by_cases hx1 : x ∈ hubs D Δ
      · exact hhub x hx1
      by_cases hx2 : x ∈ lightVerts D Δ
      · constructor
        · intro h
          have : x ∈ tieSet k π ∩ lightVerts D Δ := mem_inter.mpr ⟨h, hx2⟩
          rw [eL] at this; exact (mem_inter.mp this).1
        · intro h
          have : x ∈ tieSet k π' ∩ lightVerts D Δ := mem_inter.mpr ⟨h, hx2⟩
          rw [← eL] at this; exact (mem_inter.mp this).1
      have hr := rest_of_not_mem hx1 hx2
      rw [mem_tie_of_rest hH hp hr, mem_tie_of_rest hH hp' hr]
      constructor
      · rintro (⟨y, hy, hyT⟩ | hκ)
        · exact Or.inl ⟨y, hy, (hhub y (mem_filter.mpr ⟨mem_univ _, hr y hy⟩)).mp hyT⟩
        · exact Or.inr hκ
      · rintro (⟨y, hy, hyT⟩ | hκ)
        · exact Or.inl ⟨y, hy, (hhub y (mem_filter.mpr ⟨mem_univ _, hr y hy⟩)).mpr hyT⟩
        · exact Or.inr hκ
  have hHs : (Hs.card : ℝ) ≤ ∑ i in range (q + 1), (N.choose i : ℝ) := by
    have hsub : Hs ⊆ (range (q + 1)).biUnion fun i => (hubs D Δ).powersetCard i := by
      intro H hH'
      obtain ⟨h1, h2⟩ := mem_filter.mp hH'
      exact mem_biUnion.mpr ⟨H.card, mem_range.mpr (Nat.lt_succ_of_le h2),
        mem_powersetCard.mpr ⟨mem_powerset.mp h1, rfl⟩⟩
    have h1 := (card_le_of_subset hsub).trans card_biUnion_le
    have h2 : ∑ i in range (q + 1), ((hubs D Δ).powersetCard i).card ≤
        ∑ i in range (q + 1), N.choose i := by
      refine sum_le_sum fun i _ => ?_
      rw [card_powersetCard]
      apply Nat.choose_le_choose
      have := card_le_univ (hubs D Δ)
      rwa [Fintype.card_fin] at this
    have := h1.trans h2
    exact_mod_cast this
  have hXs : (Xs.card : ℝ) ≤ (k + 1) * (2 ^ (pstar + 1) * (6 * A) ^ k) := by
    have hsub : Xs ⊆ (range (k + 1)).biUnion fun j => (lightVerts D Δ).powersetCard j := by
      intro X hX
      obtain ⟨h1, h2⟩ := mem_filter.mp hX
      exact mem_biUnion.mpr ⟨X.card, mem_range.mpr (Nat.lt_succ_of_le h2),
        mem_powersetCard.mpr ⟨mem_powerset.mp h1, rfl⟩⟩
    have h1 := (card_le_of_subset hsub).trans card_biUnion_le
    have h1' : (Xs.card : ℝ) ≤ ∑ j in range (k + 1), ((lightVerts D Δ).card.choose j : ℝ) := by
      have : Xs.card ≤ ∑ j in range (k + 1), (lightVerts D Δ).card.choose j := by
        refine h1.trans (le_of_eq ?_)
        exact sum_congr rfl fun j _ => card_powersetCard _ _
      exact_mod_cast this
    have hn : (lightVerts D Δ).card ≤ 2 * (A * (pstar + 1) + Δ * k) := by
      have h2 : e - Δ * k < A * (pstar + 1) := by
        have := Nat.lt_mul_div_succ (e - Δ * k) (show 0 < A by omega)
        rw [hps]; simpa [mul_comm] using this
      have h3 : e ≤ A * (pstar + 1) + Δ * k := by
        generalize A * (pstar + 1) = X at h2 ⊢; generalize Δ * k = Y at h2 ⊢; omega
      exact (card_lightVerts_le D Δ).trans (Nat.mul_le_mul_left _ h3)
    calc (Xs.card : ℝ) ≤ ∑ j in range (k + 1), ((lightVerts D Δ).card.choose j : ℝ) := h1'
      _ ≤ ∑ _j in range (k + 1), (2 ^ (pstar + 1) * (6 * A) ^ k : ℝ) :=
          sum_le_sum fun j hj =>
            choose_le_aux hA1 hΔA (Nat.lt_succ_iff.mp (mem_range.mp hj)) hn
      _ = (k + 1) * (2 ^ (pstar + 1) * (6 * A) ^ k) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  -- assemble
  have hsum : (Pass.card : ℝ) * 2 ^ pstar ≤ 𝒯.card * F := by
    have h1 := card_le_of_subset hcover
    have h2 := (card_biUnion_le (s := 𝒯)
      (t := fun T => (fiber k T).filter (Balanced (DAdj D) (DKappa D) k)))
    have h3 : (∑ T in 𝒯, ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card) *
        2 ^ pstar ≤ 𝒯.card * F := by
      rw [sum_mul]
      calc ∑ T in 𝒯, ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card * 2 ^ pstar
          ≤ ∑ _T in 𝒯, F := sum_le_sum hper
        _ = 𝒯.card * F := by rw [sum_const, smul_eq_mul]
    have h4 : Pass.card * 2 ^ pstar ≤ 𝒯.card * F :=
      le_trans (Nat.mul_le_mul_right _ (h1.trans h2)) h3
    exact_mod_cast h4
  have hTr : (𝒯.card : ℝ) ≤ (∑ i in range (q + 1), (N.choose i : ℝ)) *
      ((k + 1) * (2 ^ (pstar + 1) * (6 * A) ^ k)) := by
    have : (𝒯.card : ℝ) ≤ Hs.card * Xs.card := by exact_mod_cast hTcard
    exact this.trans (mul_le_mul hHs hXs (Nat.cast_nonneg _)
      (sum_nonneg fun i _ => Nat.cast_nonneg _))
  have hpos : (0 : ℝ) < 2 ^ pstar := by positivity
  have key : (Pass.card : ℝ) * 2 ^ pstar ≤
      (2 * (k + 1) * (6 * A) ^ k * (∑ i in range (q + 1), (N.choose i : ℝ)) * F) * 2 ^ pstar := by
    calc _ ≤ (𝒯.card : ℝ) * F := hsum
      _ ≤ ((∑ i in range (q + 1), (N.choose i : ℝ)) *
            ((k + 1) * (2 ^ (pstar + 1) * (6 * A) ^ k))) * F :=
          mul_le_mul_of_nonneg_right hTr (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have := le_of_mul_le_mul_right key hpos
  push_cast at this ⊢
  exact this

end Hubs

end MaxCaterpillar.Trees
