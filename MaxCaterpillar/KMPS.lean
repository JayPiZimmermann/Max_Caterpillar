import MaxCaterpillar.CPWL

/-! # The Koutschan–Moser–Ponomarchuk–Schicho representation

Every continuous piecewise-linear function `f` on `ℝᵈ` is a `±1`-signed sum of
maxima of exactly `d + 1` affine functions, **each taken from the affine functions
`g₀, …, g_{n-1}` of any given CPWL witness of `f`**: no rescaling and no new affine
functions (Koutschan, Moser, Ponomarchuk, Schicho, *Representing piecewise linear
functions by functions with minimal arity*).

* `kmps_of_continuous_selection`: the statement for any continuous `f` such that at
  every point `x`, `f x = gᵢ(x)` for some `i` (a continuous selection of `g`);
* `kmps_pieces`: the statement for the affine functions of a `CPWLWitness` of `f`;
* `cpwl_two_hidden_layers_pieces`: for `d ≥ 2`, the corresponding two-hidden-layer
  network, with first hidden layer of width `C(n,2) + n + 1`, where `n` is the number
  of pieces of the witness, and second hidden layer of width
  `s · (secondWidth (d+1) - 2) + 2`, where `s ≤ T` is the number of distinct argument
  sets.

## Proof

1. *Crossing lemma* (`exists_cross`). For all `x, y` there is `j` with
   `gⱼ(x) ≤ f(x)` and `f(y) ≤ gⱼ(y)`. On the segment from `x` to `y`, take, among the
   affine functions selected somewhere on the segment, one of maximal slope `s`.
   A continuous function which at every point of `[0,1]` agrees with an affine function
   of slope `≤ s` satisfies `F v ≤ F u + s (v - u)` for `u ≤ v` (`slope_bound`).
2. *Max–min form* (Ovchinnikov). With `S_y = {j : f(y) ≤ gⱼ(y)}`,
   `f(x) = max_y min_{j ∈ S_y} gⱼ(x)`: the term `y = x` equals `f(x)`, and every term is
   `≤ f(x)` by the crossing lemma. Only finitely many sets `S_y` occur.
3. *Inclusion–exclusion*. `max_{S ∈ 𝒮} m_S = ∑_{∅ ≠ 𝒰 ⊆ 𝒮} (-1)^{|𝒰|+1} min_{S ∈ 𝒰} m_S`
   and `min_{j ∈ U} gⱼ = ∑_{∅ ≠ V ⊆ U} (-1)^{|V|+1} max_{j ∈ V} gⱼ`
   (`maxOn_eq_sum_minOn`, `minOn_eq_sum_maxOn`), so `f` is an integer combination of
   maxima of nonempty subfamilies of `g`.
4. *Arity reduction* (`MaxNN.exists_dominating_subset`,
   `MaxNN.maxOn_eq_sum_powerset_erase_empty`): a maximum over more than `d + 1` of the
   `gⱼ` is a `±1` combination of maxima over strictly smaller subfamilies.
5. The integer combinations of such maxima form an additive subgroup
   (`signedMaxGroup`) whose elements are exactly the `±1`-signed sums of
   `Maximum (d+1)` of `d + 1` of the `gⱼ` (subfamilies of fewer than `d + 1`
   functions are padded by repetition).

No hypothesis on the interiors of the pieces is needed: the pointwise selection
property and continuity suffice.
-/

open BigOperators

namespace MaxCaterpillar

namespace KMPS

open MaxNN

/-! ## The crossing lemma -/

/-- A continuous function on `ℝ` which at each point of `[0,1]` agrees with one of
finitely many affine functions `c i + m i * t` of slope `m i ≤ s` grows at most with
slope `s` on `[0,1]`. -/
theorem slope_bound {ι : Type _} [Finite ι] (F : ℝ → ℝ) (hF : Continuous F) (c m : ι → ℝ)
    (s : ℝ) (hsel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ i, F t = c i + m i * t ∧ m i ≤ s)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) : F v ≤ F u + s * (v - u) := by
  let A : Set ℝ := {t | F t - s * t ≤ F u - s * u}
  have hAc : IsClosed A :=
    isClosed_le (hF.sub (continuous_const.mul continuous_id)) continuous_const
  have hsub : Set.Icc u v ⊆ A := by
    refine (hAc.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin
      (le_refl (F u - s * u)) ?_
    rintro x ⟨hxA, hxu, hxv⟩
    have hev : ∀ᶠ t in nhds x, ∀ i, F x ≠ c i + m i * x → F t ≠ c i + m i * t := by
      refine Filter.eventually_all.2 fun i => ?_
      by_cases h : F x = c i + m i * x
      · exact Filter.eventually_of_forall fun t h' => absurd h h'
      · have hcont : Continuous fun t => F t - (c i + m i * t) :=
          hF.sub (continuous_const.add (continuous_const.mul continuous_id))
        have hne : (fun t => F t - (c i + m i * t)) x ≠ 0 := fun h0 => h (sub_eq_zero.mp h0)
        exact (hcont.continuousAt.eventually_ne hne).mono fun t ht _ h0 =>
          ht (sub_eq_zero.mpr h0)
    have hIoo : Set.Ioo x v ∈ nhdsWithin x (Set.Ioi x) := Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, hxv⟩
    filter_upwards [nhdsWithin_le_nhds hev, hIoo] with t ht htI
    obtain ⟨i, hi, hmi⟩ := hsel t ⟨by linarith [htI.1], by linarith [htI.2]⟩
    have hix : F x = c i + m i * x := by
      by_contra h
      exact ht i h hi
    have hxA' : F x - s * x ≤ F u - s * u := hxA
    have hneg : (m i - s) * (t - x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [htI.1])
    show F t - s * t ≤ F u - s * u
    nlinarith
  have hvA : F v - s * v ≤ F u - s * u := hsub ⟨huv, le_rfl⟩
  linarith

/-- **Crossing lemma.** Let `f` be continuous with `f x = gᵢ(x)` for some `i` at every
point. Then for all `x, y` some `gⱼ` lies weakly below `f` at `x` and weakly above `f`
at `y`. -/
theorem exists_cross {d n : ℕ} (g : Fin n → AffineFn d) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hsel : ∀ x, ∃ i, f x = (g i).eval x) (x y : Fin d → ℝ) :
    ∃ j, (g j).eval x ≤ f x ∧ f y ≤ (g j).eval y := by
  classical
  let F : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hF : Continuous F :=
    hf.comp (continuous_const.add (continuous_id.smul continuous_const))
  let m : Fin n → ℝ := fun j => ∑ l, (g j).a l * (y - x) l
  have hline : ∀ j t, (g j).eval (x + t • (y - x)) = m j * t + (g j).eval x :=
    fun j t => AffineFn.eval_line (g j) x (y - x) t
  let A : Finset (Fin n) := Finset.univ.filter
    (fun j => ∃ t ∈ Set.Icc (0 : ℝ) 1, F t = (g j).eval (x + t • (y - x)))
  have h0 : F 0 = f x := by
    show f (x + (0 : ℝ) • (y - x)) = f x
    rw [line_at_zero]
  have h1 : F 1 = f y := by
    show f (x + (1 : ℝ) • (y - x)) = f y
    rw [line_at_one]
  have hA : A.Nonempty := by
    obtain ⟨i, hi⟩ := hsel x
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, ⟨le_refl _, zero_le_one⟩, ?_⟩⟩
    rw [h0, line_at_zero]
    exact hi
  obtain ⟨j, hjA, hjmax⟩ := Finset.exists_max_image A m hA
  obtain ⟨t₀, ht₀, hFt₀⟩ := (Finset.mem_filter.mp hjA).2
  have hsel' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ i, F t = (g i).eval x + m i * t ∧ m i ≤ m j := by
    intro t ht
    obtain ⟨i, hi⟩ := hsel (x + t • (y - x))
    refine ⟨i, ?_, hjmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hi⟩)⟩
    show f (x + t • (y - x)) = _
    rw [hi, hline]
    ring
  have hb := slope_bound F hF (fun i => (g i).eval x) m (m j) hsel'
  refine ⟨j, ?_, ?_⟩
  · have h := hb 0 t₀ le_rfl ht₀.1 ht₀.2
    rw [hFt₀, hline, h0] at h
    linarith
  · have h := hb t₀ 1 ht₀.1 ht₀.2 le_rfl
    have hy : (g j).eval y = m j * 1 + (g j).eval x := by
      rw [← hline, line_at_one]
    rw [hFt₀, hline, h1] at h
    rw [hy]
    linarith

/-! ## Minima over finite index sets and inclusion–exclusion -/

/-- The minimum of `y` over a finite index set, `-maxOn A (-y)` (junk value `0` on `∅`). -/
noncomputable def minOn {ι : Type _} (A : Finset ι) (y : ι → ℝ) : ℝ :=
  -maxOn A fun i => -y i

theorem maxOn_empty {ι : Type _} (y : ι → ℝ) : maxOn (∅ : Finset ι) y = 0 :=
  dif_neg Finset.not_nonempty_empty

theorem minOn_empty {ι : Type _} (y : ι → ℝ) : minOn (∅ : Finset ι) y = 0 := by
  unfold minOn
  rw [maxOn_empty, neg_zero]

theorem minOn_singleton {ι : Type _} (a : ι) (y : ι → ℝ) : minOn {a} y = y a := by
  unfold minOn
  rw [maxOn_eq_sup' (Finset.singleton_nonempty a), Finset.sup'_singleton, neg_neg]

theorem minOn_le {ι : Type _} {A : Finset ι} (y : ι → ℝ) {j : ι} (hj : j ∈ A) :
    minOn A y ≤ y j := by
  have h : -y j ≤ maxOn A (fun i => -y i) := le_maxOn (fun i => -y i) hj
  unfold minOn
  linarith

theorem le_minOn {ι : Type _} {A : Finset ι} (h : A.Nonempty) {y : ι → ℝ} {c : ℝ}
    (hc : ∀ j ∈ A, c ≤ y j) : c ≤ minOn A y := by
  have h' : maxOn A (fun i => -y i) ≤ -c := maxOn_le h fun j hj => neg_le_neg (hc j hj)
  unfold minOn
  linarith

/-- Adding an index that dominates a nonempty set does not change the minimum. -/
theorem minOn_insert_of_le {ι : Type _} [DecidableEq ι] {V : Finset ι} (hV : V.Nonempty)
    {y : ι → ℝ} {a : ι} (ha : ∀ j ∈ V, y j ≤ y a) : minOn (insert a V) y = minOn V y := by
  refine le_antisymm (le_minOn hV fun j hj => minOn_le y (Finset.mem_insert_of_mem hj))
    (le_minOn (Finset.insert_nonempty a V) fun j hj => ?_)
  rcases Finset.mem_insert.mp hj with h | h
  · obtain ⟨j', hj'⟩ := hV
    rw [h]
    exact le_trans (minOn_le y hj') (ha j' hj')
  · exact minOn_le y h

/-- A minimum of minima over nonempty sets is the minimum over their union. -/
theorem minOn_biUnion {ι : Type _} [DecidableEq ι] {𝒰 : Finset (Finset ι)}
    (h𝒰 : 𝒰.Nonempty) (hne : ∀ S ∈ 𝒰, S.Nonempty) (y : ι → ℝ) :
    minOn 𝒰 (fun S => minOn S y) = minOn (𝒰.biUnion id) y := by
  have hU : (𝒰.biUnion id).Nonempty := by
    obtain ⟨S, hS⟩ := h𝒰
    obtain ⟨j, hj⟩ := hne S hS
    exact ⟨j, Finset.mem_biUnion.mpr ⟨S, hS, hj⟩⟩
  refine le_antisymm (le_minOn hU fun j hj => ?_) (le_minOn h𝒰 fun S hS => ?_)
  · obtain ⟨S, hS, hjS⟩ := Finset.mem_biUnion.mp hj
    exact le_trans (minOn_le (fun S => minOn S y) hS) (minOn_le y hjS)
  · exact le_minOn (hne S hS) fun j hj =>
      minOn_le y (Finset.mem_biUnion.mpr ⟨S, hS, hj⟩)

/-- **Maximum–minimum inclusion–exclusion.** For nonempty `U`,
`max_U y = ∑_{∅ ≠ V ⊆ U} (-1)^{|V|+1} min_V y`. -/
theorem maxOn_eq_sum_minOn {ι : Type _} [DecidableEq ι] {U : Finset ι} (hU : U.Nonempty)
    (y : ι → ℝ) :
    maxOn U y = ∑ V in U.powerset.erase ∅, (-1 : ℝ) ^ (V.card + 1) * minOn V y := by
  obtain ⟨j₀, hj₀, hmax⟩ := exists_maxOn_eq hU y
  let h : Finset ι → ℝ := fun V => (-1 : ℝ) ^ (V.card + 1) * minOn V y
  have hempty : h ∅ = 0 := by
    show (-1 : ℝ) ^ ((∅ : Finset ι).card + 1) * minOn ∅ y = 0
    rw [minOn_empty, mul_zero]
  have hU' : U = insert j₀ (U.erase j₀) := (Finset.insert_erase hj₀).symm
  show maxOn U y = ∑ V in U.powerset.erase ∅, h V
  rw [Finset.sum_erase _ hempty, hmax, hU',
    Finset.sum_powerset_insert (Finset.not_mem_erase j₀ U), ← Finset.sum_add_distrib]
  have hterm : ∀ V ∈ (U.erase j₀).powerset,
      h V + h (insert j₀ V) = if V = ∅ then y j₀ else 0 := by
    intro V hV
    by_cases hVe : V = ∅
    · rw [if_pos hVe, hVe, hempty, zero_add, insert_emptyc_eq]
      show (-1 : ℝ) ^ (({j₀} : Finset ι).card + 1) * minOn {j₀} y = y j₀
      rw [Finset.card_singleton, minOn_singleton]
      norm_num
    · rw [if_neg hVe]
      have hVsub : V ⊆ U.erase j₀ := Finset.mem_powerset.mp hV
      have hj₀V : j₀ ∉ V := fun hj => Finset.not_mem_erase j₀ U (hVsub hj)
      have hle : ∀ j ∈ V, y j ≤ y j₀ := fun j hj => by
        rw [← hmax]
        exact le_maxOn y (Finset.mem_of_mem_erase (hVsub hj))
      show (-1 : ℝ) ^ (V.card + 1) * minOn V y
          + (-1 : ℝ) ^ ((insert j₀ V).card + 1) * minOn (insert j₀ V) y = 0
      rw [Finset.card_insert_of_not_mem hj₀V,
        minOn_insert_of_le (Finset.nonempty_of_ne_empty hVe) hle, pow_succ (-1 : ℝ) (V.card + 1)]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ (∅ : Finset ι),
    if_pos (Finset.empty_mem_powerset _)]

/-- **Minimum–maximum inclusion–exclusion.** For nonempty `U`,
`min_U y = ∑_{∅ ≠ V ⊆ U} (-1)^{|V|+1} max_V y`. -/
theorem minOn_eq_sum_maxOn {ι : Type _} [DecidableEq ι] {U : Finset ι} (hU : U.Nonempty)
    (y : ι → ℝ) :
    minOn U y = ∑ V in U.powerset.erase ∅, (-1 : ℝ) ^ (V.card + 1) * maxOn V y := by
  have h := maxOn_eq_sum_minOn hU fun i => -y i
  have e : ∀ V : Finset ι, minOn V (fun i => -y i) = -maxOn V y := by
    intro V
    unfold minOn
    have e' : (fun i => -(fun i => -y i) i) = y := funext fun i => neg_neg (y i)
    rw [e']
  unfold minOn
  rw [h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [e V]
  ring

/-! ## Signed sums of maxima of `d + 1` of the given affine functions -/

/-- The `±1`-signed sums `∑ₜ εₜ Maximum (d+1) (g_{αₜ 0}, …, g_{αₜ d})` of maxima of
`d + 1` of the affine functions `g`, as an additive subgroup of the functions on `ℝᵈ`. -/
def signedMaxGroup {d n : ℕ} (g : Fin n → AffineFn d) :
    AddSubgroup ((Fin d → ℝ) → ℝ) where
  carrier := {h | ∃ (T : ℕ) (ε : Fin T → ℝ) (α : Fin T → Fin (d + 1) → Fin n),
    (∀ t, ε t = 1 ∨ ε t = -1) ∧
    ∀ x, h x = ∑ t, ε t * Maximum (d + 1) (fun i => (g (α t i)).eval x)}
  zero_mem' := ⟨0, Fin.elim0, fun t => t.elim0, fun t => t.elim0, fun x => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    rfl⟩
  add_mem' := by
    rintro h₁ h₂ ⟨T₁, ε₁, α₁, hε₁, hr₁⟩ ⟨T₂, ε₂, α₂, hε₂, hr₂⟩
    refine ⟨T₁ + T₂, Fin.append ε₁ ε₂, Fin.append α₁ α₂, fun t => ?_, fun x => ?_⟩
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
      · rw [Fin.append_left]
        exact hε₁ t
      · rw [Fin.append_right]
        exact hε₂ t
    · show h₁ x + h₂ x = _
      rw [Fin.sum_univ_add, hr₁ x, hr₂ x]
      simp only [Fin.append_left, Fin.append_right]
  neg_mem' := by
    rintro h ⟨T, ε, α, hε, hr⟩
    refine ⟨T, fun t => -ε t, α, fun t => ?_, fun x => ?_⟩
    · rcases hε t with e | e
      · right
        show -ε t = -1
        rw [e]
      · left
        show -ε t = 1
        rw [e, neg_neg]
    · show -h x = _
      rw [hr x, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring

theorem signed_mem_signedMaxGroup {d n : ℕ} (g : Fin n → AffineFn d)
    {h : (Fin d → ℝ) → ℝ} (hh : h ∈ signedMaxGroup g) (k : ℕ) :
    (fun x => (-1 : ℝ) ^ k * h x) ∈ signedMaxGroup g := by
  rcases neg_one_pow_eq_or ℝ k with e | e
  · have e' : (fun x => (-1 : ℝ) ^ k * h x) = h := funext fun x => by rw [e, one_mul]
    rw [e']
    exact hh
  · have e' : (fun x => (-1 : ℝ) ^ k * h x) = -h := funext fun x => by
      rw [e, neg_one_mul]
      rfl
    rw [e']
    exact (signedMaxGroup g).neg_mem hh

theorem sum_mem_signedMaxGroup {d n : ℕ} (g : Fin n → AffineFn d) {κ : Type _}
    (s : Finset κ) (φ : κ → (Fin d → ℝ) → ℝ) (hφ : ∀ c ∈ s, φ c ∈ signedMaxGroup g) :
    (fun x => ∑ c in s, φ c x) ∈ signedMaxGroup g := by
  have e : (fun x => ∑ c in s, φ c x) = ∑ c in s, φ c :=
    funext fun x => (Finset.sum_apply x s φ).symm
  rw [e]
  exact AddSubgroup.sum_mem _ hφ

/-- A maximum over a nonempty set of at most `d + 1` of the `gⱼ` is a single term. -/
theorem maxOn_mem_signedMaxGroup_of_card_le {d n : ℕ} (g : Fin n → AffineFn d)
    {A : Finset (Fin n)} (hA : A.Nonempty) (hcard : A.card ≤ d + 1) :
    (fun x => maxOn A fun j => (g j).eval x) ∈ signedMaxGroup g := by
  obtain ⟨j₀, hj₀⟩ := hA
  let α₀ : Fin (d + 1) → Fin n := fun i =>
    if h : (i : ℕ) < A.card then (A.equivFin.symm ⟨i, h⟩ : Fin n) else j₀
  have hmem : ∀ i, α₀ i ∈ A := by
    intro i
    by_cases h : (i : ℕ) < A.card
    · show (if h : (i : ℕ) < A.card then (A.equivFin.symm ⟨i, h⟩ : Fin n) else j₀) ∈ A
      rw [dif_pos h]
      exact (A.equivFin.symm ⟨i, h⟩).2
    · show (if h : (i : ℕ) < A.card then (A.equivFin.symm ⟨i, h⟩ : Fin n) else j₀) ∈ A
      rw [dif_neg h]
      exact hj₀
  have hsurj : ∀ j ∈ A, ∃ i, α₀ i = j := by
    intro j hj
    let k := A.equivFin ⟨j, hj⟩
    have hk : (k : ℕ) < A.card := k.2
    refine ⟨⟨k, by omega⟩, ?_⟩
    show (if h : ((⟨k, _⟩ : Fin (d + 1)) : ℕ) < A.card
      then (A.equivFin.symm ⟨_, h⟩ : Fin n) else j₀) = j
    rw [dif_pos hk]
    have e : A.equivFin.symm ⟨(k : ℕ), hk⟩ = ⟨j, hj⟩ := by
      rw [Fin.eta]
      exact Equiv.symm_apply_apply _ _
    rw [e]
  refine ⟨1, fun _ => 1, fun _ => α₀, fun _ => Or.inl rfl, fun x => ?_⟩
  rw [Fin.sum_univ_one, one_mul]
  show maxOn A (fun j => (g j).eval x) = MAX (d + 1) (fun i => (g (α₀ i)).eval x)
  refine le_antisymm (maxOn_le ⟨j₀, hj₀⟩ fun j hj => ?_)
    (MAX_le fun i => le_maxOn (fun j => (g j).eval x) (hmem i))
  obtain ⟨i, hi⟩ := hsurj j hj
  rw [← hi]
  exact le_MAX (d + 1) (fun i => (g (α₀ i)).eval x) i

/-- **Integer arity reduction.** The maximum of any nonempty subfamily of the `gⱼ` is a
`±1`-signed sum of maxima of `d + 1` of the `gⱼ`. -/
theorem maxOn_mem_signedMaxGroup {d n : ℕ} (g : Fin n → AffineFn d) (N : ℕ) :
    ∀ S : Finset (Fin n), S.card = N → S.Nonempty →
      (fun x => maxOn S fun j => (g j).eval x) ∈ signedMaxGroup g := by
  classical
  refine Nat.strong_induction_on N ?_
  intro N ih S hSN hS
  rcases le_or_lt S.card (d + 1) with hle | hlt
  · exact maxOn_mem_signedMaxGroup_of_card_le g hS hle
  · obtain ⟨J, hJS, hSJ, hdom⟩ := exists_dominating_subset g S hlt
    have e : (fun x => maxOn S fun j => (g j).eval x)
        = fun x => ∑ T in J.powerset.erase ∅,
            (fun T x => (-1 : ℝ) ^ (T.card + 1) * maxOn (S \ T) fun j => (g j).eval x) T x := by
      funext x
      obtain ⟨j₀, hj₀, hle⟩ := hdom x
      exact maxOn_eq_sum_powerset_erase_empty (fun j => (g j).eval x) S J hJS hSJ hj₀ hle
    rw [e]
    refine sum_mem_signedMaxGroup g _ _ fun T hT => signed_mem_signedMaxGroup g ?_ _
    have hT' := Finset.mem_erase.mp hT
    have hTJ : T ⊆ J := Finset.mem_powerset.mp hT'.2
    have hTne : T.Nonempty := Finset.nonempty_of_ne_empty hT'.1
    have hsub : S \ J ⊆ S \ T := Finset.sdiff_subset_sdiff (Finset.Subset.refl S) hTJ
    have hlt' : (S \ T).card < N := by
      rw [← hSN, Finset.card_sdiff (hTJ.trans hJS)]
      exact Nat.sub_lt (Finset.card_pos.mpr hS) (Finset.card_pos.mpr hTne)
    exact ih _ hlt' (S \ T) rfl (hSJ.mono hsub)

/-! ## The max–min form and the main theorem -/

/-- **Max–min form (Ovchinnikov).** A continuous selection `f` of the affine functions
`g` is the maximum, over the finitely many sets `S_y = {j : f(y) ≤ gⱼ(y)}`, of the
minimum of the `gⱼ`, `j ∈ S_y`. -/
theorem eq_maxOn_minOn {d n : ℕ} (g : Fin n → AffineFn d) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hsel : ∀ x, ∃ i, f x = (g i).eval x) :
    ∃ 𝒮 : Finset (Finset (Fin n)), 𝒮.Nonempty ∧ (∀ S ∈ 𝒮, S.Nonempty) ∧
      ∀ x, f x = maxOn 𝒮 fun S => minOn S fun j => (g j).eval x := by
  classical
  let Sy : (Fin d → ℝ) → Finset (Fin n) := fun y => Finset.univ.filter fun j => f y ≤ (g j).eval y
  have hSy : ∀ y, ∃ i ∈ Sy y, f y = (g i).eval y := by
    intro y
    obtain ⟨i, hi⟩ := hsel y
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_eq hi⟩, hi⟩
  let 𝒮 : Finset (Finset (Fin n)) := Finset.univ.filter fun S => ∃ y, Sy y = S
  have hmem : ∀ y, Sy y ∈ 𝒮 := fun y => Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, rfl⟩
  have hne : ∀ S ∈ 𝒮, S.Nonempty := by
    intro S hS
    obtain ⟨y, rfl⟩ := (Finset.mem_filter.mp hS).2
    obtain ⟨i, hi, _⟩ := hSy y
    exact ⟨i, hi⟩
  refine ⟨𝒮, ⟨Sy 0, hmem 0⟩, hne, fun x => le_antisymm ?_ ?_⟩
  · refine le_trans ?_ (le_maxOn (fun S => minOn S fun j => (g j).eval x) (hmem x))
    obtain ⟨i, hi, _⟩ := hSy x
    exact le_minOn ⟨i, hi⟩ fun j hj => (Finset.mem_filter.mp hj).2
  · refine maxOn_le ⟨Sy 0, hmem 0⟩ fun S hS => ?_
    obtain ⟨y, rfl⟩ := (Finset.mem_filter.mp hS).2
    obtain ⟨j, hjx, hjy⟩ := exists_cross g hf hsel x y
    exact le_trans (minOn_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjy⟩)) hjx

end KMPS

open KMPS

/-- **KMPS representation for continuous selections.** Let `f : ℝᵈ → ℝ` be continuous
and suppose that at every point `x`, `f x = gᵢ(x)` for some `i`. Then `f` is a
`±1`-signed sum of maxima of exactly `d + 1` of the affine functions `g₀, …, g_{n-1}`
themselves. -/
theorem kmps_of_continuous_selection {d n : ℕ} (g : Fin n → MaxNN.AffineFn d)
    (f : Point d → ℝ) (hf : Continuous f) (hsel : ∀ x, ∃ i, f x = (g i).eval x) :
    ∃ (T : ℕ) (ε : Fin T → ℝ) (α : Fin T → Fin (d + 1) → Fin n),
      (∀ t, ε t = 1 ∨ ε t = -1) ∧
      ∀ x, f x = ∑ t, ε t * Maximum (d + 1) (fun i => (g (α t i)).eval x) := by
  classical
  obtain ⟨𝒮, h𝒮, hne, hrep⟩ := eq_maxOn_minOn g hf hsel
  have e : f = fun x => ∑ 𝒰 in 𝒮.powerset.erase ∅,
      (fun 𝒰 x => (-1 : ℝ) ^ (𝒰.card + 1) *
        (fun x => ∑ V in (𝒰.biUnion id).powerset.erase ∅,
          (fun V x => (-1 : ℝ) ^ (V.card + 1) * MaxNN.maxOn V fun j => (g j).eval x) V x) x)
        𝒰 x := by
    funext x
    rw [hrep x, maxOn_eq_sum_minOn h𝒮]
    refine Finset.sum_congr rfl fun 𝒰 h𝒰 => ?_
    have h𝒰' := Finset.mem_erase.mp h𝒰
    have h𝒰sub : 𝒰 ⊆ 𝒮 := Finset.mem_powerset.mp h𝒰'.2
    have h𝒰ne : 𝒰.Nonempty := Finset.nonempty_of_ne_empty h𝒰'.1
    have hne' : ∀ S ∈ 𝒰, S.Nonempty := fun S hS => hne S (h𝒰sub hS)
    have hU : (𝒰.biUnion id).Nonempty := by
      obtain ⟨S, hS⟩ := h𝒰ne
      obtain ⟨j, hj⟩ := hne' S hS
      exact ⟨j, Finset.mem_biUnion.mpr ⟨S, hS, hj⟩⟩
    show (-1 : ℝ) ^ (𝒰.card + 1) * minOn 𝒰 (fun S => minOn S fun j => (g j).eval x) = _
    rw [minOn_biUnion h𝒰ne hne', minOn_eq_sum_maxOn hU]
  have hmem : f ∈ signedMaxGroup g := by
    rw [e]
    refine sum_mem_signedMaxGroup g _ _ fun 𝒰 _ => signed_mem_signedMaxGroup g ?_ _
    refine sum_mem_signedMaxGroup g _ _ fun V hV => signed_mem_signedMaxGroup g ?_ _
    exact maxOn_mem_signedMaxGroup g _ V rfl
      (Finset.nonempty_of_ne_empty (Finset.mem_erase.mp hV).1)
  exact hmem

/-- **Koutschan–Moser–Ponomarchuk–Schicho representation.** Let `W` be any CPWL witness
of `f ∈ CPWL d`, with affine functions `W.g a`, `a < W.n`. Then `f` is a `±1`-signed sum
of maxima of exactly `d + 1` of these affine functions: no rescaling and no new affine
functions are used. -/
theorem kmps_pieces (d : ℕ) (f : Point d → ℝ) (hf : f ∈ MaxNN.CPWL d)
    (W : MaxNN.CPWLWitness d f) :
    ∃ (T : ℕ) (ε : Fin T → ℝ) (α : Fin T → Fin (d + 1) → Fin W.n),
      (∀ t, ε t = 1 ∨ ε t = -1) ∧
      ∀ x, f x = ∑ t, ε t * Maximum (d + 1)
        (fun i => (∑ l, (W.g (α t i)).a l * x l) + (W.g (α t i)).c) :=
  kmps_of_continuous_selection W.g f hf.1 fun x => by
    obtain ⟨i, hi⟩ := W.covers x
    exact ⟨i, W.agrees i x hi⟩

/-- **CPWL functions, pieces of a witness.** For `d ≥ 2`, let `W` be any CPWL witness of
`f ∈ CPWL d`, with `n = W.n` pieces and affine functions `g_a(x) = ∑ₗ (W.g a).a l xₗ +
(W.g a).c`. Then `f = ∑ₜ εₜ max_{d+1}(g_{αₜ 0}, …, g_{αₜ d})` with signs `εₜ = ±1`, and
`f` is computed by a two-hidden-layer network whose first hidden layer has width
`C(n,2) + n + 1` and whose second hidden layer has width
`s · (secondWidth (d+1) - 2) + 2`, where `s ≤ T` is the number of distinct argument sets
`{αₜ i : i}`. -/
theorem cpwl_two_hidden_layers_pieces (d : ℕ) (hd : 2 ≤ d) (f : Point d → ℝ)
    (hf : f ∈ MaxNN.CPWL d) (W : MaxNN.CPWLWitness d f) :
    ∃ (T : ℕ) (α : Fin T → Fin (d + 1) → Fin W.n) (ε : Fin T → ℝ),
      (∀ t, ε t = 1 ∨ ε t = -1) ∧
      (∀ x, f x = ∑ t, ε t * Maximum (d + 1)
        (fun i => (∑ l, (W.g (α t i)).a l * x l) + (W.g (α t i)).c)) ∧
      ∃ s : ℕ, s = (Finset.univ.image fun t => Finset.univ.image (α t)).card ∧ s ≤ T ∧
        ∃ net : Network d (W.n.choose 2 + W.n + 1) (s * (secondWidth (d + 1) - 2) + 2),
          ∀ x, net.eval x = f x := by
  obtain ⟨T, ε, α, hε, hrep⟩ := kmps_pieces d f hf W
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  obtain ⟨net, hnet⟩ := caterpillar_shared_pieces_any r (by omega)
    (fun a => (W.g a).a) (fun a => (W.g a).c) α ε
  exact ⟨T, α, ε, hε, hrep, _, rfl, card_imageSets_le α, net,
    fun x => (hnet x).trans (hrep x).symm⟩

end MaxCaterpillar
