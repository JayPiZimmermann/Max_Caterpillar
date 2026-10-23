import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-! # Subspaces on which `max + min` is linear

For a finite index set `s` and a subspace `V ⊆ ℝ^ι`, suppose that `max_s x + min_s x = L x` for all
`x ∈ V`, with `L` linear. Then `dim V ≤ dim (V ∩ {x = 0 on s}) + ⌊|s|/2⌋ + 1`
(`finrank_le_of_maxmin`). For `s = ι` this says `dim V ≤ ⌊|ι|/2⌋ + 1`
(`finrank_le_of_maxmin_univ`); the bound is attained by `{x₀ + x₁ = x₂ + x₃ = …}`.

Proof by induction on `|s|`. If two coordinates of `s` agree on all of `V`, drop one. Otherwise a
generic `v ∈ V` has a unique maximal coordinate `a` and a unique minimal coordinate `b` on `s`;
comparing `x + t v` for large `t` gives `L x = x_a + x_b` on `V`. On the hyperplane
`V' = V ∩ {x_a = x_b}` the coordinates `a, b` lie between the maximum and the minimum, so
`max + min` over `s \ {a, b}` equals `2 x_a` there; the induction hypothesis applies to `V'`.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators FiniteDimensional Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction of a function on `ι` to the coordinates in `s`. -/
def restr (s : Finset ι) : (ι → ℝ) →ₗ[ℝ] (s → ℝ) where
  toFun x i := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The functions vanishing on `s`. -/
def zeroOn (s : Finset ι) : Submodule ℝ (ι → ℝ) := LinearMap.ker (restr s)

lemma mem_zeroOn (s : Finset ι) (x : ι → ℝ) : x ∈ zeroOn s ↔ ∀ i ∈ s, x i = 0 := by
  constructor
  · intro h i hi
    have := congr_fun (LinearMap.mem_ker.1 h) ⟨i, hi⟩
    exact this
  · intro h
    exact LinearMap.mem_ker.2 (funext fun i => h i i.2)

lemma finrank_le_inf_zeroOn (V : Submodule ℝ (ι → ℝ)) (s : Finset ι) :
    finrank ℝ V ≤ finrank ℝ (V ⊓ zeroOn s : Submodule ℝ (ι → ℝ)) + s.card := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V (zeroOn s)
  have h2 : finrank ℝ (V ⊔ zeroOn s : Submodule ℝ (ι → ℝ)) ≤ Fintype.card ι := by
    have := Submodule.finrank_le (V ⊔ zeroOn s)
    rwa [finrank_fintype_fun_eq_card] at this
  have h3 := LinearMap.finrank_range_add_finrank_ker (restr s)
  have h4 : finrank ℝ (LinearMap.range (restr s)) ≤ s.card := by
    have := Submodule.finrank_le (LinearMap.range (restr s))
    rwa [finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  rw [finrank_fintype_fun_eq_card] at h3
  have h5 : finrank ℝ (zeroOn s) = finrank ℝ (LinearMap.ker (restr s)) := rfl
  linarith

lemma finrank_le_inf_ker (V : Submodule ℝ (ι → ℝ)) (φ : (ι → ℝ) →ₗ[ℝ] ℝ) :
    finrank ℝ V ≤ finrank ℝ (V ⊓ LinearMap.ker φ : Submodule ℝ (ι → ℝ)) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V (LinearMap.ker φ)
  have h2 : finrank ℝ (V ⊔ LinearMap.ker φ : Submodule ℝ (ι → ℝ)) ≤ Fintype.card ι := by
    have := Submodule.finrank_le (V ⊔ LinearMap.ker φ)
    rwa [finrank_fintype_fun_eq_card] at this
  have h3 := LinearMap.finrank_range_add_finrank_ker φ
  have h4 : finrank ℝ (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    rwa [finrank_self] at this
  rw [finrank_fintype_fun_eq_card] at h3
  linarith

/-- A vector of `V` separating every pair of coordinates that `V` separates. -/
lemma exists_generic (V : Submodule ℝ (ι → ℝ)) (P : Finset (ι × ι))
    (hP : ∀ p ∈ P, ∃ x ∈ V, x p.1 ≠ x p.2) : ∃ v ∈ V, ∀ p ∈ P, v p.1 ≠ v p.2 := by
  induction P using Finset.induction_on with
  | empty => exact ⟨0, V.zero_mem, fun p hp => absurd hp (Finset.not_mem_empty p)⟩
  | @insert p P hpP ih =>
    obtain ⟨v, hvV, hv⟩ := ih fun r hr => hP r (Finset.mem_insert_of_mem hr)
    obtain ⟨u, huV, hu⟩ := hP p (Finset.mem_insert_self p P)
    let bad : Finset ℝ :=
      (insert p P).image fun r => -(v r.1 - v r.2) / (u r.1 - u r.2)
    obtain ⟨t, ht⟩ := Infinite.exists_not_mem_finset bad
    refine ⟨v + t • u, V.add_mem hvV (V.smul_mem t huV), fun r hr => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    intro heq
    by_cases hur : u r.1 = u r.2
    · have hr' : r ∈ P := by
        rcases Finset.mem_insert.1 hr with h | h
        · exact absurd (h ▸ hur) hu
        · exact h
      apply hv r hr'
      rw [hur] at heq; linarith
    · apply ht
      refine Finset.mem_image.2 ⟨r, hr, ?_⟩
      have hne : u r.1 - u r.2 ≠ 0 := sub_ne_zero.2 hur
      field_simp
      linarith

/-- If `v` has a unique maximal coordinate `a` and a unique minimal coordinate `b` on `s`, then
`L = x_a + x_b` on `V`. -/
lemma L_eq_of_extreme (s : Finset ι) (hs : s.Nonempty) (V : Submodule ℝ (ι → ℝ))
    (L : (ι → ℝ) →ₗ[ℝ] ℝ) (h : ∀ x ∈ V, s.sup' hs x + s.inf' hs x = L x)
    (v : ι → ℝ) (hv : v ∈ V) (a b : ι) (ha : a ∈ s) (hb : b ∈ s)
    (hva : ∀ k ∈ s, k ≠ a → v k < v a) (hvb : ∀ k ∈ s, k ≠ b → v b < v k)
    (x : ι → ℝ) (hx : x ∈ V) : L x = x a + x b := by
  have hev : ∀ᶠ t : ℝ in atTop, (∀ k ∈ s, k ≠ a → x k + t * v k < x a + t * v a) ∧
      (∀ k ∈ s, k ≠ b → x b + t * v b < x k + t * v k) := by
    refine ((Filter.eventually_all_finset s).2 fun k hk => ?_).and
      ((Filter.eventually_all_finset s).2 fun k hk => ?_)
    · by_cases hka : k = a
      · exact Filter.eventually_of_forall fun t h => absurd hka h
      · have hpos : 0 < v a - v k := sub_pos.2 (hva k hk hka)
        filter_upwards [(Filter.tendsto_id.atTop_mul_const hpos).eventually_gt_atTop
          (x k - x a)] with t ht _
        simp only [id] at ht
        nlinarith
    · by_cases hkb : k = b
      · exact Filter.eventually_of_forall fun t h => absurd hkb h
      · have hpos : 0 < v k - v b := sub_pos.2 (hvb k hk hkb)
        filter_upwards [(Filter.tendsto_id.atTop_mul_const hpos).eventually_gt_atTop
          (x b - x k)] with t ht _
        simp only [id] at ht
        nlinarith
  obtain ⟨t, hta, htb⟩ := hev.exists
  have e1 : s.sup' hs (x + t • v) = x a + t * v a := by
    refine le_antisymm (Finset.sup'_le hs _ fun k hk => ?_) ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hka : k = a
      · rw [hka]
      · exact (hta k hk hka).le
    · have := Finset.le_sup' (x + t • v) ha
      simpa using this
  have e2 : s.inf' hs (x + t • v) = x b + t * v b := by
    refine le_antisymm ?_ (Finset.le_inf' hs _ fun k hk => ?_)
    · have := Finset.inf'_le (x + t • v) hb
      simpa using this
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hkb : k = b
      · rw [hkb]
      · exact (htb k hk hkb).le
  have e3 : s.sup' hs v = v a := by
    refine le_antisymm (Finset.sup'_le hs _ fun k hk => ?_) (Finset.le_sup' v ha)
    by_cases hka : k = a
    · rw [hka]
    · exact (hva k hk hka).le
  have e4 : s.inf' hs v = v b := by
    refine le_antisymm (Finset.inf'_le v hb) (Finset.le_inf' hs _ fun k hk => ?_)
    by_cases hkb : k = b
    · rw [hkb]
    · exact (hvb k hk hkb).le
  have hxv := h (x + t • v) (V.add_mem hx (V.smul_mem t hv))
  have hvv := h v hv
  rw [e1, e2, map_add, map_smul, smul_eq_mul] at hxv
  rw [e3, e4] at hvv
  rw [← hvv] at hxv
  linarith

/-- **Lemma 3.** If `max_s + min_s` is linear on `V`, then
`dim V ≤ dim (V ∩ {x = 0 on s}) + ⌊|s|/2⌋ + 1`. -/
theorem finrank_le_of_maxmin (n : ℕ) : ∀ (s : Finset ι) (hs : s.Nonempty)
    (V : Submodule ℝ (ι → ℝ)) (L : (ι → ℝ) →ₗ[ℝ] ℝ), s.card = n →
    (∀ x ∈ V, s.sup' hs x + s.inf' hs x = L x) →
    finrank ℝ V ≤ finrank ℝ (V ⊓ zeroOn s : Submodule ℝ (ι → ℝ)) + n / 2 + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs V L hn h
  by_cases hA : ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ ∀ x ∈ V, x i = x j
  · -- two coordinates agree on `V`: drop one of them
    obtain ⟨i, hi, j, hj, hij, hV⟩ := hA
    have hs' : (s.erase j).Nonempty := ⟨i, Finset.mem_erase.2 ⟨hij, hi⟩⟩
    have hcard : (s.erase j).card = n - 1 := by rw [Finset.card_erase_of_mem hj, hn]
    have hn1 : 1 ≤ n := by rw [← hn]; exact Finset.card_pos.2 hs
    have hsup : ∀ x ∈ V, (s.erase j).sup' hs' x = s.sup' hs x := by
      intro x hx
      refine le_antisymm (Finset.sup'_le _ _ fun k hk =>
        Finset.le_sup' x (Finset.mem_of_mem_erase hk)) (Finset.sup'_le _ _ fun k hk => ?_)
      by_cases hkj : k = j
      · rw [hkj, ← hV x hx]; exact Finset.le_sup' x (Finset.mem_erase.2 ⟨hij, hi⟩)
      · exact Finset.le_sup' x (Finset.mem_erase.2 ⟨hkj, hk⟩)
    have hinf : ∀ x ∈ V, (s.erase j).inf' hs' x = s.inf' hs x := by
      intro x hx
      refine le_antisymm (Finset.le_inf' _ _ fun k hk => ?_) (Finset.le_inf' _ _ fun k hk =>
        Finset.inf'_le x (Finset.mem_of_mem_erase hk))
      by_cases hkj : k = j
      · rw [hkj, ← hV x hx]; exact Finset.inf'_le x (Finset.mem_erase.2 ⟨hij, hi⟩)
      · exact Finset.inf'_le x (Finset.mem_erase.2 ⟨hkj, hk⟩)
    have IH := ih (n - 1) (by omega) (s.erase j) hs' V L hcard fun x hx => by
      rw [hsup x hx, hinf x hx]; exact h x hx
    have hK : (V ⊓ zeroOn (s.erase j) : Submodule ℝ (ι → ℝ)) = V ⊓ zeroOn s := by
      ext x
      simp only [Submodule.mem_inf, mem_zeroOn]
      constructor
      · rintro ⟨hx, hz⟩
        refine ⟨hx, fun k hk => ?_⟩
        by_cases hkj : k = j
        · rw [hkj, ← hV x hx]; exact hz i (Finset.mem_erase.2 ⟨hij, hi⟩)
        · exact hz k (Finset.mem_erase.2 ⟨hkj, hk⟩)
      · rintro ⟨hx, hz⟩
        exact ⟨hx, fun k hk => hz k (Finset.mem_of_mem_erase hk)⟩
    rw [hK] at IH
    have : (n - 1) / 2 ≤ n / 2 := Nat.div_le_div_right (Nat.sub_le n 1)
    linarith
  · push_neg at hA
    by_cases hn2 : n ≤ 2
    · have := finrank_le_inf_zeroOn V s
      rw [hn] at this
      have : n ≤ n / 2 + 1 := by omega
      linarith
    · push_neg at hn2
      -- a generic vector
      obtain ⟨v, hvV, hv⟩ := exists_generic V ((s ×ˢ s).filter fun p => p.1 ≠ p.2)
        fun p hp => by
          simp only [Finset.mem_filter, Finset.mem_product] at hp
          by_contra hc
          push_neg at hc
          exact (hA p.1 hp.1.1 p.2 hp.1.2 hp.2).elim fun x hx => hx.2 (hc x hx.1)
      have hvne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i ≠ v j := fun i hi j hj hij =>
        hv (i, j) (by simp [hi, hj, hij])
      obtain ⟨a, ha, hamax⟩ := Finset.exists_max_image s v hs
      obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image s v hs
      have hva : ∀ k ∈ s, k ≠ a → v k < v a := fun k hk hka =>
        lt_of_le_of_ne (hamax k hk) (hvne k hk a ha hka)
      have hvb : ∀ k ∈ s, k ≠ b → v b < v k := fun k hk hkb =>
        lt_of_le_of_ne (hbmin k hk) (hvne k hk b hb hkb).symm
      have hab : a ≠ b := by
        intro e
        obtain ⟨k, hk, hka⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < s.card) a
        have h1 := hva k hk hka
        have h2 := hvb k hk (e ▸ hka)
        rw [e] at h1; linarith
      have hL := L_eq_of_extreme s hs V L h v hvV a b ha hb hva hvb
      -- the hyperplane `x_a = x_b`
      let φ : (ι → ℝ) →ₗ[ℝ] ℝ :=
        (LinearMap.proj a : (ι → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj b : (ι → ℝ) →ₗ[ℝ] ℝ)
      have hφ : ∀ x, φ x = x a - x b := fun x => rfl
      let V' : Submodule ℝ (ι → ℝ) := V ⊓ LinearMap.ker φ
      have hmemV' : ∀ x, x ∈ V' ↔ x ∈ V ∧ x a = x b := fun x => by
        simp only [V', Submodule.mem_inf, LinearMap.mem_ker, hφ, sub_eq_zero]
      let s' := (s.erase a).erase b
      have hs'mem : ∀ k, k ∈ s' ↔ k ∈ s ∧ k ≠ a ∧ k ≠ b := fun k => by
        simp only [s', Finset.mem_erase]; tauto
      have hcard : s'.card = n - 2 := by
        simp only [s']
        rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hab.symm, hb⟩),
          Finset.card_erase_of_mem ha, hn]
        omega
      have hs' : s'.Nonempty := Finset.card_pos.1 (by omega)
      -- `max + min` over `s'` is `2 x_a` on `V'`
      have hV' : ∀ x ∈ V', s'.sup' hs' x + s'.inf' hs' x =
          ((2 : ℝ) • (LinearMap.proj a : (ι → ℝ) →ₗ[ℝ] ℝ)) x := by
        intro x hx
        obtain ⟨hxV, hxab⟩ := (hmemV' x).1 hx
        simp only [LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, smul_eq_mul]
        have hsum : s.sup' hs x + s.inf' hs x = 2 * x a := by
          rw [h x hxV, hL x hxV, hxab]; ring
        have hm : s.inf' hs x ≤ x a := Finset.inf'_le x ha
        have hM : x a ≤ s.sup' hs x := Finset.le_sup' x ha
        have hsub : ∀ k ∈ s', k ∈ s := fun k hk => ((hs'mem k).1 hk).1
        have up : s'.sup' hs' x ≤ s.sup' hs x :=
          Finset.sup'_le _ _ fun k hk => Finset.le_sup' x (hsub k hk)
        have lo : s.inf' hs x ≤ s'.inf' hs' x :=
          Finset.le_inf' _ _ fun k hk => Finset.inf'_le x (hsub k hk)
        rcases eq_or_lt_of_le hM with hMa | hMa
        · -- `x` is constant on `s`
          have hcst : ∀ k ∈ s, x k = x a := fun k hk => by
            have := Finset.le_sup' x hk
            have := Finset.inf'_le x hk
            linarith
          obtain ⟨k0, hk0⟩ := id hs'
          have e1 : s'.sup' hs' x = x a := le_antisymm
            (Finset.sup'_le _ _ fun k hk => (hcst k (hsub k hk)).le)
            ((hcst k0 (hsub k0 hk0)).symm.le.trans (Finset.le_sup' x hk0))
          have e2 : s'.inf' hs' x = x a := le_antisymm
            ((Finset.inf'_le x hk0).trans (hcst k0 (hsub k0 hk0)).le)
            (Finset.le_inf' _ _ fun k hk => (hcst k (hsub k hk)).symm.le)
          rw [e1, e2]; ring
        · rcases eq_or_lt_of_le hm with hma | hma
          · have hcst : ∀ k ∈ s, x k = x a := fun k hk => by
              have := Finset.le_sup' x hk
              have := Finset.inf'_le x hk
              linarith
            obtain ⟨k0, hk0⟩ := id hs'
            have e1 : s'.sup' hs' x = x a := le_antisymm
              (Finset.sup'_le _ _ fun k hk => (hcst k (hsub k hk)).le)
              ((hcst k0 (hsub k0 hk0)).symm.le.trans (Finset.le_sup' x hk0))
            have e2 : s'.inf' hs' x = x a := le_antisymm
              ((Finset.inf'_le x hk0).trans (hcst k0 (hsub k0 hk0)).le)
              (Finset.le_inf' _ _ fun k hk => (hcst k (hsub k hk)).symm.le)
            rw [e1, e2]; ring
          · -- `x_a = x_b` lies strictly between the extremes
            obtain ⟨kM, hkM, hkMe⟩ := Finset.exists_mem_eq_sup' hs x
            obtain ⟨km, hkm, hkme⟩ := Finset.exists_mem_eq_inf' hs x
            have hkM' : kM ∈ s' := (hs'mem kM).2 ⟨hkM, fun e => by rw [e] at hkMe; linarith,
              fun e => by rw [e, ← hxab] at hkMe; linarith⟩
            have hkm' : km ∈ s' := (hs'mem km).2 ⟨hkm, fun e => by rw [e] at hkme; linarith,
              fun e => by rw [e, ← hxab] at hkme; linarith⟩
            have e1 : s'.sup' hs' x = s.sup' hs x :=
              le_antisymm up (hkMe ▸ Finset.le_sup' x hkM')
            have e2 : s'.inf' hs' x = s.inf' hs x :=
              le_antisymm (hkme ▸ Finset.inf'_le x hkm') lo
            rw [e1, e2, hsum]
      have IH := ih (n - 2) (by omega) s' hs' V' _ hcard hV'
      -- the kernel does not grow
      have hK : (V' ⊓ zeroOn s' : Submodule ℝ (ι → ℝ)) ≤ V ⊓ zeroOn s := by
        intro x hx
        rw [Submodule.mem_inf, mem_zeroOn] at hx ⊢
        obtain ⟨hx', hz⟩ := hx
        obtain ⟨hxV, hxab⟩ := (hmemV' x).1 hx'
        have hxa : x a = 0 := by
          obtain ⟨k0, hk0⟩ := id hs'
          have hk0s := ((hs'mem k0).1 hk0).1
          have hsum : s.sup' hs x + s.inf' hs x = 2 * x a := by
            rw [h x hxV, hL x hxV, hxab]; ring
          have hval : ∀ k ∈ s, x k = 0 ∨ x k = x a := fun k hk => by
            by_cases hka : k = a
            · right; rw [hka]
            · by_cases hkb : k = b
              · right; rw [hkb, hxab]
              · left; exact hz k ((hs'mem k).2 ⟨hk, hka, hkb⟩)
          have hz0 : x k0 = 0 := hz k0 hk0
          rcases le_total 0 (x a) with hpos | hneg
          · have e1 : s.sup' hs x = x a := le_antisymm
              (Finset.sup'_le _ _ fun k hk => by
                rcases hval k hk with h' | h' <;> rw [h'] ; exact hpos)
              (Finset.le_sup' x ha)
            have e2 : s.inf' hs x = 0 := le_antisymm (hz0 ▸ Finset.inf'_le x hk0s)
              (Finset.le_inf' _ _ fun k hk => by
                rcases hval k hk with h' | h' <;> rw [h'] ; exact hpos)
            rw [e1, e2] at hsum; linarith
          · have e1 : s.sup' hs x = 0 := le_antisymm
              (Finset.sup'_le _ _ fun k hk => by
                rcases hval k hk with h' | h' <;> rw [h'] ; exact hneg)
              (hz0 ▸ Finset.le_sup' x hk0s)
            have e2 : s.inf' hs x = x a := le_antisymm (Finset.inf'_le x ha)
              (Finset.le_inf' _ _ fun k hk => by
                rcases hval k hk with h' | h' <;> rw [h'] ; exact hneg)
            rw [e1, e2] at hsum; linarith
        refine ⟨hxV, fun k hk => ?_⟩
        by_cases hka : k = a
        · rw [hka, hxa]
        · by_cases hkb : k = b
          · rw [hkb, ← hxab, hxa]
          · exact hz k ((hs'mem k).2 ⟨hk, hka, hkb⟩)
      have h1 := Submodule.finrank_mono hK
      have h2 := finrank_le_inf_ker V φ
      have h3 : (n - 2) / 2 + 1 = n / 2 := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        simp [Nat.add_div_right]
      linarith

/-- **Lemma 3 (whole index set).** If `max + min` is linear on `V ⊆ ℝ^ι`, then
`dim V ≤ ⌊|ι|/2⌋ + 1`. -/
theorem finrank_le_of_maxmin_univ [Nonempty ι] (V : Submodule ℝ (ι → ℝ))
    (L : (ι → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ x ∈ V, Finset.univ.sup' Finset.univ_nonempty x +
      Finset.univ.inf' Finset.univ_nonempty x = L x) :
    finrank ℝ V ≤ Fintype.card ι / 2 + 1 := by
  have := finrank_le_of_maxmin _ Finset.univ Finset.univ_nonempty V L rfl h
  have hK : (V ⊓ zeroOn Finset.univ : Submodule ℝ (ι → ℝ)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, mem_zeroOn] at hx
    rw [Submodule.mem_bot]
    exact funext fun i => hx.2 i (Finset.mem_univ i)
  rw [hK, finrank_bot, Finset.card_univ] at this
  linarith

end Frontier
end MaxCaterpillar
