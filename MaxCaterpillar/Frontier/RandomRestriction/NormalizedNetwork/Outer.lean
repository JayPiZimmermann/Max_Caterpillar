import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Directional

/-! # Freeze outer gates and restore translation normalization

Positive outer gates are absorbed into the linear and first-hidden-layer
output terms, negative gates disappear, and zero gates retain their original
indices. The first rows never change. A second diagonal pass therefore needs
only translation invariance of those first rows, not of the outer skips.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators Filter Topology
variable {N h₁ h₂ : ℕ}

/-- The exact outer gate rule for any prescribed gate values. -/
noncomputable def freezeOuter (net : NormalizedNetwork N h₁ h₂) (β : Fin h₂ → ℝ) :
    NormalizedNetwork N h₁ h₂ where
  A := net.A
  U k := if β k = 0 then net.U k else 0
  W k j := if β k = 0 then net.W k j else 0
  L := net.L + ∑ k, if 0 < β k then net.d k • net.U k else 0
  B j := net.B j + ∑ k, if 0 < β k then net.d k * net.W k j else 0
  d k := if β k = 0 then net.d k else 0

@[simp] theorem freezeOuter_first_row (net : NormalizedNetwork N h₁ h₂)
    (β : Fin h₂ → ℝ) (j : Fin h₁) : (freezeOuter net β).A j = net.A j := rfl

lemma freezeOuter_inner (net : NormalizedNetwork N h₁ h₂) (β : Fin h₂ → ℝ)
    (k : Fin h₂) (x : Point N) :
    (freezeOuter net β).inner k x = if β k = 0 then net.inner k x else 0 := by
  classical
  by_cases hk : β k = 0 <;> simp [inner,freezeOuter,hk,lin_zero_left]

lemma freezeOuter_linear_output (net : NormalizedNetwork N h₁ h₂) (β : Fin h₂ → ℝ)
    (x : Point N) :
    lin (freezeOuter net β).L x +
        (∑ j, (freezeOuter net β).B j * relu (lin (net.A j) x)) =
      lin net.L x + (∑ j, net.B j * relu (lin (net.A j) x)) +
        ∑ k, if 0 < β k then net.d k * net.inner k x else 0 := by
  classical
  have hlin : lin (freezeOuter net β).L x = lin net.L x +
      ∑ k, if 0 < β k then net.d k * lin (net.U k) x else 0 := by
    change lin (net.L + ∑ k, if 0 < β k then net.d k • net.U k else 0) x = _
    rw [lin_add_left,lin_sum_left]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp [lin_smul_left,lin_zero_left]
  have hfirst : (∑ j, (freezeOuter net β).B j * relu (lin (net.A j) x)) =
      (∑ j, net.B j * relu (lin (net.A j) x)) +
        ∑ k, if 0 < β k then net.d k *
          (∑ j, net.W k j * relu (lin (net.A j) x)) else 0 := by
    simp only [freezeOuter,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
    congr 1
    calc
      (∑ j, ∑ k, (if 0 < β k then net.d k * net.W k j else 0) *
          relu (lin (net.A j) x)) =
          ∑ k, ∑ j, (if 0 < β k then net.d k * net.W k j else 0) *
            relu (lin (net.A j) x) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : 0 < β k <;> simp [hk,Finset.mul_sum,mul_assoc]
  have hsum : (∑ k, if 0 < β k then net.d k * lin (net.U k) x else 0) +
      (∑ k, if 0 < β k then net.d k *
        (∑ j, net.W k j * relu (lin (net.A j) x)) else 0) =
      ∑ k, if 0 < β k then net.d k * net.inner k x else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : 0 < β k <;> simp [hk,inner,mul_add]
  rw [hlin,hfirst]
  linarith only [hsum]

/-- An algebraic identity for arbitrary networks and arbitrary outer gates. -/
theorem freezeOuter_eval (net : NormalizedNetwork N h₁ h₂) (β : Fin h₂ → ℝ)
    (x : Point N) :
    (freezeOuter net β).eval x =
      lin net.L x + (∑ j, net.B j * relu (lin (net.A j) x)) +
        ∑ k, net.d k * pick (β k) (net.inner k x) (relu (net.inner k x)) := by
  classical
  rw [eval]
  simp only [freezeOuter_first_row]
  rw [freezeOuter_linear_output]
  have hsum : (∑ k, if 0 < β k then net.d k * net.inner k x else 0) +
      (∑ k, (freezeOuter net β).d k * relu ((freezeOuter net β).inner k x)) =
      ∑ k, net.d k * pick (β k) (net.inner k x) (relu (net.inner k x)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [freezeOuter_inner]
    rcases lt_trichotomy (β k) 0 with hk | hk | hk
    · simp [freezeOuter,pick,hk,not_lt.mpr hk.le,hk.ne]
    · simp [freezeOuter,pick,hk]
    · simp [freezeOuter,pick,hk,ne_of_gt hk]
  linarith only [hsum]

/-- Masking outer slots cannot introduce a new first-hidden feeding index. -/
theorem freezeOuter_feeding_original (net : NormalizedNetwork N h₁ h₂)
    (β : Fin h₂ → ℝ) (j : Fin h₁) (hj : (freezeOuter net β).Feeding j) :
    net.Feeding j := by
  obtain ⟨k,hk⟩ := hj
  refine ⟨k,?_⟩
  intro hz
  exact hk (by simp [freezeOuter,hz])

/-- Reapply the all-ones rule only to the outer gates, retaining every first row. -/
noncomputable def normalizeOuter (net : NormalizedNetwork N h₁ h₂) :
    NormalizedNetwork N h₁ h₂ := freezeOuter net (fun k => ∑ i, net.U k i)

@[simp] theorem normalizeOuter_first_row (net : NormalizedNetwork N h₁ h₂)
    (j : Fin h₁) : (normalizeOuter net).A j = net.A j := rfl

noncomputable def outerSlope (net : NormalizedNetwork N h₁ h₂) : ℝ :=
  (∑ i, net.L i) + ∑ k, net.d k * pick (∑ i, net.U k i) (∑ i, net.U k i) 0

lemma inner_add_diag_of_first_zero_sum (net : NormalizedNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i, net.A j i = 0) (k : Fin h₂) (x : Point N) (t : ℝ) :
    net.inner k (x + diag t) = net.inner k x + t * ∑ i, net.U k i := by
  have hfirst (j : Fin h₁) : lin (net.A j) (x + diag t) = lin (net.A j) x := by
    rw [lin_add_right,lin_diag,hA j,mul_zero,add_zero]
  unfold inner
  simp only [hfirst]
  rw [lin_add_right,lin_diag]
  ring

/-- Exact diagonal asymptotics with no zero-sum assumption on outer skips. -/
theorem eventually_eval_normalizeOuter (net : NormalizedNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i, net.A j i = 0) (x : Point N) :
    ∀ᶠ t in atTop,
      net.eval (x + diag t) = t * outerSlope net + (normalizeOuter net).eval x := by
  have hsecond : ∀ᶠ t in atTop, ∀ k,
      relu (net.inner k x + t * ∑ i, net.U k i) =
        pick (∑ i, net.U k i) (net.inner k x + t * ∑ i, net.U k i)
          (relu (net.inner k x)) :=
    Filter.eventually_all.mpr (fun k => eventually_relu _ _)
  filter_upwards [hsecond] with t hsecond
  have hfirst (j : Fin h₁) : lin (net.A j) (x + diag t) = lin (net.A j) x := by
    rw [lin_add_right,lin_diag,hA j,mul_zero,add_zero]
  have hsum : (∑ k, net.d k *
      pick (∑ i, net.U k i) (net.inner k x + t * ∑ i, net.U k i)
        (relu (net.inner k x))) =
      t * (∑ k, net.d k * pick (∑ i, net.U k i) (∑ i, net.U k i) 0) +
        ∑ k, net.d k * pick (∑ i, net.U k i) (net.inner k x) (relu (net.inner k x)) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold pick
    split_ifs <;> ring
  rw [normalizeOuter,freezeOuter_eval]
  simp only [eval,hfirst,
    inner_add_diag_of_first_zero_sum net hA,hsecond,outerSlope]
  rw [lin_add_right,lin_diag,hsum]
  ring

/-- Both the unit diagonal slope and the restored all-input maximum equation
follow from only the original equation and zero sums of the first rows. -/
theorem normalizeOuter_max_and_slope [NeZero N] (net : NormalizedNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i, net.A j i = 0) (hnet : ∀ x, net.eval x = Maximum N x) :
    outerSlope net = 1 ∧ ∀ x, (normalizeOuter net).eval x = Maximum N x := by
  have key : ∀ x, outerSlope net = 1 ∧ (normalizeOuter net).eval x = Maximum N x := by
    intro x
    apply affine_eq_of_eventually
    filter_upwards [eventually_eval_normalizeOuter net hA x] with t ht
    rw [← ht,hnet,Maximum_add_diag]
    ring
  exact ⟨(key 0).1,fun x => (key x).2⟩

theorem normalizeOuter_computes_max [NeZero N] (net : NormalizedNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i, net.A j i = 0) (hnet : ∀ x, net.eval x = Maximum N x) :
    ∀ x, (normalizeOuter net).eval x = Maximum N x :=
  (normalizeOuter_max_and_slope net hA hnet).2

lemma normalizeOuter_output_sum (net : NormalizedNetwork N h₁ h₂) :
    (∑ i, (normalizeOuter net).L i) = outerSlope net := by
  classical
  have he : (∑ i, (normalizeOuter net).L i) = lin (normalizeOuter net).L (diag 1) := by
    rw [lin_diag,one_mul]
  rw [he]
  change lin (net.L + ∑ k, if 0 < ∑ i, net.U k i then net.d k • net.U k else 0)
    (diag 1) = _
  rw [lin_add_left,lin_sum_left,lin_diag,one_mul]
  unfold outerSlope
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 0 < ∑ i, net.U k i
  · rw [if_pos hk,lin_smul_left,lin_diag,one_mul]
    simp [pick,hk]
  · simp [hk,pick,lin_zero_left]

/-- The all-ones pass restores zero-sum outer skips without assuming them. -/
theorem normalizeOuter_translation_normalized [NeZero N]
    (net : NormalizedNetwork N h₁ h₂) (hA : ∀ j, ∑ i, net.A j i = 0)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    (normalizeOuter net).TranslationNormalized := by
  classical
  refine ⟨hA,?_,?_⟩
  · intro k
    by_cases hk : (∑ i, net.U k i) = 0
    · simpa only [normalizeOuter,freezeOuter,hk,ite_true] using hk
    · simp [normalizeOuter,freezeOuter,hk]
  · rw [normalizeOuter_output_sum]
    exact (normalizeOuter_max_and_slope net hA hnet).1

theorem normalizeOuter_feeding_original (net : NormalizedNetwork N h₁ h₂)
    (j : Fin h₁) (hj : (normalizeOuter net).Feeding j) : net.Feeding j :=
  freezeOuter_feeding_original net _ j hj

#check @freezeOuter_eval
#check @normalizeOuter_computes_max
#check @normalizeOuter_translation_normalized
#print axioms freezeOuter_eval
#print axioms normalizeOuter_computes_max
#print axioms normalizeOuter_translation_normalized
#print axioms normalizeOuter_feeding_original
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
