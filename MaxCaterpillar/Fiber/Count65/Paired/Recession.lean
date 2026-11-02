import MaxCaterpillar.Fiber.Count65.Paired.Normalization
import MaxCaterpillar.Fiber.First65.TwoIncrement

/-!
# Recession atom extraction from arbitrary paired-domain completions

The hypothesis is the actual max-of-two identity on all nonnegative independent
increments. No recession pattern, nonzero output coefficient, distinct knot,
or atom cancellation condition is assumed.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Filter Topology Frontier

variable {m : ℕ}

/-- The common-increment slope must be one. -/
theorem common_increment_slope (a b : ℝ) (d C α β : Fin m → ℝ)
    (h : ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a+q) (b+r) = ∑ k, d k*relu (C k+α k*q+β k*r)) :
    (∑ k, d k*relu (α k+β k)) = 1 := by
  have ht := eventually_weighted_relu d C (fun k => α k+β k)
  have he : ∀ᶠ t in atTop,
      t*1+max a b = t*(∑ k, d k*pick (α k+β k) (α k+β k) 0) +
        ∑ k, d k*pick (α k+β k) (C k) (relu (C k)) := by
    filter_upwards [ht, eventually_ge_atTop (0 : ℝ)] with t htail ht0
    have hh := h t t ht0 ht0
    have hforms : (∑ k, d k*relu (C k+α k*t+β k*t)) =
        ∑ k, d k*relu (C k+t*(α k+β k)) := by
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      ring
    rw [max_add_add_right, hforms, htail] at hh
    linarith only [hh]
  have hs := (affine_eq_of_eventually he).1
  calc
    _ = ∑ k, d k*pick (α k+β k) (α k+β k) 0 := by
      apply Finset.sum_congr rfl
      intro k _
      unfold pick
      rcases lt_trichotomy (α k+β k) 0 with hk | hk | hk
      · rw [if_neg (not_lt.mpr hk.le), if_pos hk, relu_of_nonpos hk.le]
      · rw [hk]
        simp [relu]
      · rw [if_pos hk, relu_of_nonneg hk.le]
    _ = 1 := hs.symm

/-- A genuine positive-common-slope gate is forced, hence at most four of
five gates can supply nonconstant zero-common-slope atoms. -/
theorem exists_positive_common_slope (a b : ℝ) (d C α β : Fin m → ℝ)
    (h : ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a+q) (b+r) = ∑ k, d k*relu (C k+α k*q+β k*r)) :
    ∃ k, 0 < α k+β k := by
  have hs := common_increment_slope a b d C α β h
  by_contra hn
  push_neg at hn
  have hz : ∀ k, relu (α k+β k) = 0 := fun k => relu_of_nonpos (hn k)
  simp only [hz, mul_zero, Finset.sum_const_zero] at hs
  norm_num at hs

/-- The effective scalar atoms of a paired-domain completion. -/
noncomputable def activeAtoms (d α β : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun k => α k+β k=0 ∧ α k≠0 ∧ d k≠0

theorem activeAtoms_card_le_four (a b : ℝ) (d C α β : Fin m → ℝ)
    (hm : m ≤ 5)
    (h : ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a+q) (b+r) = ∑ k, d k*relu (C k+α k*q+β k*r)) :
    (activeAtoms d α β).card ≤ 4 := by
  obtain ⟨k, hk⟩ := exists_positive_common_slope a b d C α β h
  have hsub : activeAtoms d α β ⊆ Finset.univ.erase k := by
    intro i hi
    have hi0 := (Finset.mem_filter.mp hi).2.1
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hik
    subst i
    linarith only [hk, hi0]
  have hc := Finset.card_le_of_subset hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin] at hc
  have hm0 : 1 ≤ m := Nat.succ_le_of_lt
    (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)
  have he : m-1+1=m := Nat.sub_add_cancel hm0
  linarith only [hc, hm, he]

/-- Exact normalized atom balance, extracted from the paired-domain max
identity. All zero gates and zero difference slopes are retained safely. -/
theorem atomBalance_of_two_increment_max (a b : ℝ) (d C α β : Fin m → ℝ)
    (h : ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a+q) (b+r) = ∑ k, d k*relu (C k+α k*q+β k*r)) :
    Paired65.AtomBalance
      (fun k => (if α k+β k=0 then d k else 0)*|α k|)
      (fun k => -(C k+α k*(b-a))/α k) := by
  let δ : Fin m → ℝ := fun k => if α k+β k=0 then d k else 0
  let C' : Fin m → ℝ := fun k => C k+α k*(b-a)
  let A : ℝ := ∑ k, if 0<α k+β k then d k*α k else 0
  let B : ℝ := ∑ k, if 0<α k+β k then d k*C' k else 0
  apply atomBalance_of_general_affine_relu_identity δ C' α (-A) (b-B)
  intro t
  have hr := two_increment_recession a b d C α β h (t+(b-a))
  have ht : max (a+(t+(b-a))) b = relu t+b := by
    calc
      max (a+(t+(b-a))) b = max (t+b) (0+b) := by congr 1 <;> ring
      _ = max t 0+b := max_add_add_right t 0 b
      _ = relu t+b := by rw [max_comm t 0]; rfl
  have hforms : ∀ k, C k+(t+(b-a))*α k = C' k+α k*t := by
    intro k
    dsimp only [C']
    ring
  rw [ht] at hr
  simp_rw [hforms] at hr
  have he : (∑ k, d k*pick (α k+β k) (C' k+α k*t)
      (relu (C' k+α k*t))) =
      (∑ k, δ k*relu (C' k+α k*t)) + A*t+B := by
    simp only [δ, A, B, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold pick
    rcases lt_trichotomy (α k+β k) 0 with hk | hk | hk
    · simp [hk, hk.ne, not_lt.mpr hk.le]
    · simp only [hk, lt_irrefl, if_false, if_true]
      ring
    · simp only [if_pos hk, if_neg hk.ne']
      ring
  rw [he] at hr
  nlinarith only [hr]

end MaxCaterpillar.Fiber.Count65.Paired
