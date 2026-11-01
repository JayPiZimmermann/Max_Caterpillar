import MaxCaterpillar.Frontier.Asymptotics

/-! # A unique pair of diagonal carriers must be opposite

If an exact bias-free Max network has just one first row of positive diagonal
slope and one of negative slope, those rows lie on opposite rays. Otherwise
both carrier activations vanish along a nontrivial diagonal segment, whereas
the target changes on that segment. No restriction on the second width is used.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Frontier

open BigOperators

variable {N h₁ h₂ : ℕ}

/-- Equal first hidden states give equal outputs, for every suffix. -/
theorem ZNet.eval_eq_of_first_activations_eq (net : ZNet N h₁ h₂)
    {x y : Point N}
    (hxy : ∀ j, relu (lin (net.A j) x) = relu (lin (net.A j) y)) :
    net.eval x = net.eval y := by
  simp only [ZNet.eval, hxy]

/-- When the two normalized carrier values are ordered in this direction,
the corresponding two diagonal shifts have exactly the same first hidden
state. Exact representation of the maximum therefore forces equality. -/
theorem ZNet.single_carriers_eq_of_le [NeZero N]
    (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (p q : Fin h₁) (hp : 0 < net.s p) (hq : net.s q < 0)
    (hother : ∀ j, j ≠ p → j ≠ q → net.s j = 0)
    (x : Point N)
    (hab : lin (net.A p) x / net.s p ≤ lin (net.A q) x / net.s q) :
    lin (net.A p) x / net.s p = lin (net.A q) x / net.s q := by
  set a := lin (net.A p) x / net.s p
  set b := lin (net.A q) x / net.s q
  have hpval : lin (net.A p) x = a * net.s p := by
    dsimp [a]
    rw [div_mul_cancel _ hp.ne']
  have hqval : lin (net.A q) x = b * net.s q := by
    dsimp [b]
    rw [div_mul_cancel _ hq.ne]
  have hab' : a ≤ b := hab
  have he : net.eval (x + diag (-a)) = net.eval (x + diag (-b)) := by
    apply net.eval_eq_of_first_activations_eq
    intro j
    rw [net.lin_add_diag, net.lin_add_diag]
    by_cases hjp : j = p
    · subst j
      have hleft : lin (net.A p) x + -a * net.s p = 0 := by
        rw [hpval]
        ring
      have hright : lin (net.A p) x + -b * net.s p ≤ 0 := by
        rw [hpval]
        have hprod := mul_le_mul_of_nonneg_right hab' hp.le
        linarith
      rw [hleft, relu_of_nonpos le_rfl, relu_of_nonpos hright]
    · by_cases hjq : j = q
      · subst j
        have hleft : lin (net.A q) x + -a * net.s q ≤ 0 := by
          rw [hqval]
          have hprod := mul_le_mul_of_nonpos_right hab' hq.le
          linarith
        have hright : lin (net.A q) x + -b * net.s q = 0 := by
          rw [hqval]
          ring
        rw [relu_of_nonpos hleft, hright, relu_of_nonpos le_rfl]
      · rw [hother j hjp hjq, mul_zero, mul_zero]
  rw [h, h, Maximum_add_diag, Maximum_add_diag] at he
  change a = b
  linarith

/-- A single positive and a single negative first diagonal carrier have the
same normalized linear form. The other first rows are translation invariant. -/
theorem ZNet.normalized_single_carriers_eq [NeZero N]
    (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (p q : Fin h₁) (hp : 0 < net.s p) (hq : net.s q < 0)
    (hother : ∀ j, j ≠ p → j ≠ q → net.s j = 0) (x : Point N) :
    lin (net.A p) x / net.s p = lin (net.A q) x / net.s q := by
  rcases le_total (lin (net.A p) x / net.s p)
      (lin (net.A q) x / net.s q) with hab | hba
  · exact net.single_carriers_eq_of_le h p q hp hq hother x hab
  · have he := net.single_carriers_eq_of_le h p q hp hq hother (-x) (by
      simp only [lin_neg_right, neg_div]
      exact neg_le_neg hba)
    simpa only [lin_neg_right, neg_div, neg_inj] using he

/-- The unique negative first carrier is the negative scalar multiple of the
unique positive one dictated by their diagonal slopes. -/
theorem ZNet.single_carrier_rows_proportional [NeZero N]
    (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (p q : Fin h₁) (hp : 0 < net.s p) (hq : net.s q < 0)
    (hother : ∀ j, j ≠ p → j ≠ q → net.s j = 0) :
    net.A q = (net.s q / net.s p) • net.A p := by
  funext i
  have he := net.normalized_single_carriers_eq h p q hp hq hother (unitVec i)
  simp only [lin_unitVec] at he
  have hcross := (div_eq_div_iff hp.ne' hq.ne).mp he
  simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
  apply (eq_div_iff hp.ne').mpr
  nlinarith only [hcross]

/-- The carrier proportionality conclusion also applies to arbitrary biases,
because every exact Max network has the same exact recession network. -/
theorem single_carrier_rows_proportional [NeZero N]
    (net : Network N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (p q : Fin h₁) (hp : 0 < net.toZ.s p) (hq : net.toZ.s q < 0)
    (hother : ∀ j, j ≠ p → j ≠ q → net.toZ.s j = 0) :
    net.W₁ q = (net.toZ.s q / net.toZ.s p) • net.W₁ p :=
  net.toZ.single_carrier_rows_proportional (net.toZ_eval_of_max h) p q hp hq hother

/-- With a unique positive first carrier, the invariant first rows determine
the input modulo its common diagonal translation. -/
theorem ZNet.invariant_kernel_eq_diag_of_single_positive [NeZero N]
    (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (p : Fin h₁) (hp : 0 < net.s p)
    (hunique : ∀ j, 0 < net.s j → j = p) (w : Point N)
    (hw : ∀ j, net.s j = 0 → lin (net.A j) w = 0) :
    w = diag (lin (net.A p) w / net.s p) := by
  apply sub_eq_zero.mp
  apply net.ker_plus h
  intro j hj
  rw [lin_sub_right, lin_diag]
  change lin (net.A j) w - (lin (net.A p) w / net.s p) * net.s j = 0
  by_cases hjp : j = p
  · subst j
    rw [div_mul_cancel _ hp.ne', sub_self]
  · have hs : net.s j = 0 := by
      apply le_antisymm _ hj
      apply not_lt.mp
      intro hpos
      exact hjp (hunique j hpos)
    rw [hw j hs, hs, mul_zero, sub_self]

/-- The common kernel of invariant first rows is exactly the diagonal when
there is a unique positive carrier. This uses no bound on either width. -/
theorem ZNet.invariant_kernel_iff_diag_of_single_positive [NeZero N]
    (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (p : Fin h₁) (hp : 0 < net.s p)
    (hunique : ∀ j, 0 < net.s j → j = p) (w : Point N) :
    (∀ j, net.s j = 0 → lin (net.A j) w = 0) ↔ ∃ t : ℝ, w = diag t := by
  constructor
  · intro hw
    exact ⟨lin (net.A p) w / net.s p,
      net.invariant_kernel_eq_diag_of_single_positive h p hp hunique w hw⟩
  · rintro ⟨t, rfl⟩ j hj
    rw [lin_diag]
    change t * net.s j = 0
    rw [hj, mul_zero]

end Frontier
end MaxCaterpillar
