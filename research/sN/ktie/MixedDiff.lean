import Mathlib.Tactic

/-! # The k-fold mixed difference at a k-tie, and the double count

For a finite set `T` of coordinates, a base point `p` and a step `δ`,
`Λ_T f = ∑_{S ⊆ T} (-1)^{|S|} f(p + δ 1_S)`.

* `mixedDiff_eq_zero_of_indep`: `Λ_T` kills every function that does not
  depend on some coordinate `i ∈ T` (all first-hidden-layer functions
  `σ(±x_i)`, `σ(x_i - x_j)` and all linear functions once `|T| ≥ 3`).
* `mixedDiff_eq_of_tie`, `mixedDiff_max`: at a point where `T` ties at the top
  and every other coordinate lies at least `δ` below, `Λ_T max = -δ ≠ 0`.
* `mixedDiff_sum`: linearity.
* `double_count`: if every locality is served by at least `s` members of `K`
  and every member serves at most `m` localities, then `s · #L ≤ |K| · m`.

Research file for the k-tie route (research/sN/ktie); not imported by the
library.
-/

open BigOperators Finset

noncomputable section

namespace KTie

variable {ι : Type*} [DecidableEq ι]

/-- `p + δ 1_S`. -/
def shift (p : ι → ℝ) (δ : ℝ) (S : Finset ι) : ι → ℝ :=
  fun o => p o + if o ∈ S then δ else 0

/-- The mixed difference `∑_{S ⊆ T} (-1)^{|S|} f(p + δ 1_S)`. -/
def mixedDiff (T : Finset ι) (f : (ι → ℝ) → ℝ) (p : ι → ℝ) (δ : ℝ) : ℝ :=
  ∑ S in T.powerset, (-1 : ℝ) ^ S.card * f (shift p δ S)

/-- `f` does not depend on the coordinate `i`. -/
def IndepOf (f : (ι → ℝ) → ℝ) (i : ι) : Prop :=
  ∀ x c, f (Function.update x i c) = f x

theorem shift_insert (p : ι → ℝ) (δ : ℝ) (S : Finset ι) (i : ι) :
    shift p δ (insert i S) = Function.update (shift p δ S) i (p i + δ) := by
  ext o
  by_cases h : o = i
  · subst h; simp [shift]
  · simp [shift, h, Function.update_noteq]

theorem mixedDiff_eq_zero_of_indep {T : Finset ι} {f : (ι → ℝ) → ℝ} {i : ι}
    (hi : i ∈ T) (hf : IndepOf f i) (p : ι → ℝ) (δ : ℝ) : mixedDiff T f p δ = 0 := by
  obtain ⟨T', hT', rfl⟩ : ∃ T', i ∉ T' ∧ T = insert i T' :=
    ⟨T.erase i, not_mem_erase i T, (insert_erase hi).symm⟩
  unfold mixedDiff
  rw [sum_powerset_insert hT', ← sum_add_distrib]
  apply sum_eq_zero
  intro S hS
  have hiS : i ∉ S := fun h => hT' (mem_powerset.1 hS h)
  rw [card_insert_of_not_mem hiS, shift_insert, hf]
  ring

theorem mixedDiff_add (T : Finset ι) (f g : (ι → ℝ) → ℝ) (p : ι → ℝ) (δ : ℝ) :
    mixedDiff T (fun x => f x + g x) p δ = mixedDiff T f p δ + mixedDiff T g p δ := by
  unfold mixedDiff
  rw [← sum_add_distrib]
  exact sum_congr rfl fun S _ => by ring

theorem mixedDiff_smul (T : Finset ι) (c : ℝ) (f : (ι → ℝ) → ℝ) (p : ι → ℝ) (δ : ℝ) :
    mixedDiff T (fun x => c * f x) p δ = c * mixedDiff T f p δ := by
  unfold mixedDiff
  rw [mul_sum]
  exact sum_congr rfl fun S _ => by ring

theorem mixedDiff_sum {α : Type*} (T : Finset ι) (A : Finset α) (f : α → (ι → ℝ) → ℝ)
    (p : ι → ℝ) (δ : ℝ) :
    mixedDiff T (fun x => ∑ a in A, f a x) p δ = ∑ a in A, mixedDiff T (f a) p δ := by
  unfold mixedDiff
  simp_rw [mul_sum]
  exact sum_comm

/-- Functions that are sums of functions each independent of a coordinate of `T`
are killed. -/
theorem mixedDiff_eq_zero_of_sum_indep {α : Type*} {T : Finset ι} (A : Finset α)
    (f : α → (ι → ℝ) → ℝ) (hf : ∀ a ∈ A, ∃ i ∈ T, IndepOf (f a) i) (p : ι → ℝ) (δ : ℝ) :
    mixedDiff T (fun x => ∑ a in A, f a x) p δ = 0 := by
  rw [mixedDiff_sum]
  apply sum_eq_zero
  intro a ha
  obtain ⟨i, hi, hind⟩ := hf a ha
  exact mixedDiff_eq_zero_of_indep hi hind p δ

theorem sum_powerset_neg_one_pow_real {T : Finset ι} (hT : T.Nonempty) :
    (∑ S in T.powerset, (-1 : ℝ) ^ S.card) = 0 := by
  have h := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card_of_nonempty hT)
  push_cast at h
  exact h

/-- If `f(p + δ 1_S) = c + δ [S ≠ ∅]` for every `S ⊆ T`, then `Λ_T f = -δ`. -/
theorem mixedDiff_eq_of_tie {T : Finset ι} (hT : T.Nonempty) (f : (ι → ℝ) → ℝ)
    (p : ι → ℝ) (c δ : ℝ)
    (hf : ∀ S ⊆ T, f (shift p δ S) = c + δ - if S = ∅ then δ else 0) :
    mixedDiff T f p δ = -δ := by
  unfold mixedDiff
  rw [sum_congr rfl fun S hS => by rw [hf S (mem_powerset.1 hS)]]
  simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, sum_powerset_neg_one_pow_real hT, zero_mul,
    mul_ite, mul_zero]
  rw [sum_ite_eq' T.powerset ∅ (fun S => (-1 : ℝ) ^ S.card * δ)]
  simp

/-- The maximum of all coordinates. -/
def maxN [Fintype ι] (hι : (Finset.univ : Finset ι).Nonempty) (y : ι → ℝ) : ℝ :=
  Finset.univ.sup' hι y

/-- At a `k`-tie: `p = 0` on `T`, `p ≤ -δ` off `T`, `δ ≥ 0`.  Then
`Λ_T max = -δ`. -/
theorem mixedDiff_max [Fintype ι] (hι : (Finset.univ : Finset ι).Nonempty) {T : Finset ι}
    (hT : T.Nonempty) (p : ι → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpT : ∀ t ∈ T, p t = 0) (hpo : ∀ o, o ∉ T → p o ≤ -δ) :
    mixedDiff T (maxN hι) p δ = -δ := by
  apply mixedDiff_eq_of_tie hT _ p 0 δ
  intro S hS
  obtain ⟨t0, ht0⟩ := hT
  have hle : ∀ o, shift p δ S o ≤ (if S = ∅ then 0 else δ) := by
    intro o
    by_cases ho : o ∈ T
    · have hpo0 := hpT o ho
      by_cases hoS : o ∈ S
      · have hne : S ≠ ∅ := ne_empty_of_mem hoS
        simp [shift, hoS, hpo0, hne]
      · by_cases hS0 : S = ∅ <;> simp [shift, hoS, hpo0, hS0, hδ]
    · have hoS : o ∉ S := fun h => ho (hS h)
      have := hpo o ho
      by_cases hS0 : S = ∅ <;> simp [shift, hoS, hS0] <;> linarith
  have hge : ∃ o, shift p δ S o = (if S = ∅ then 0 else δ) := by
    by_cases hS0 : S = ∅
    · refine ⟨t0, ?_⟩
      simp [shift, hS0, hpT t0 ht0]
    · obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.2 hS0
      refine ⟨s, ?_⟩
      simp [shift, hs, hS0, hpT s (hS hs)]
  have hmax : maxN hι (shift p δ S) = (if S = ∅ then 0 else δ) := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun o _ => hle o
    · obtain ⟨o, ho⟩ := hge
      rw [← ho]
      exact Finset.le_sup' _ (Finset.mem_univ o)
  rw [hmax]
  by_cases hS0 : S = ∅ <;> simp [hS0]

/-- Double counting: every locality served by at least `s` members of `K`, every
member serving at most `m` localities, gives `s · #L ≤ |K| · m`. -/
theorem double_count {U L : Type*} [Fintype L] (K : Finset U) (serves : U → L → Prop)
    [∀ u l, Decidable (serves u l)] (s m : ℕ)
    (hL : ∀ l, s ≤ (K.filter fun u => serves u l).card)
    (hU : ∀ u ∈ K, (Finset.univ.filter fun l => serves u l).card ≤ m) :
    s * Fintype.card L ≤ K.card * m := by
  have h1 : s * Fintype.card L ≤ ∑ l : L, (K.filter fun u => serves u l).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum fun l _ => hL l
  have h2 : (∑ l : L, (K.filter fun u => serves u l).card) =
      ∑ u in K, (Finset.univ.filter fun l => serves u l).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : (∑ u in K, (Finset.univ.filter fun l => serves u l).card) ≤ K.card * m := by
    calc (∑ u in K, (Finset.univ.filter fun l => serves u l).card) ≤ ∑ _u in K, m :=
          Finset.sum_le_sum hU
      _ = K.card * m := by rw [Finset.sum_const, smul_eq_mul]
  exact le_trans h1 (h2 ▸ h3)

end KTie
