import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # A finite bounded-size-bias Laplace estimate

This is the finite-sum form of the negative-parameter estimate in
Arratia--Baxendale, arXiv:1306.0157, Proposition 4.1. Its assumptions are the
standard size-bias identity and a pointwise bounded coupling, not a tail
bound. Constructing those assumptions for actual permutations is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def finiteLaplace (p X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ ω, p ω * Real.exp (t * X ω)

def FiniteSizeBiasIdentity (p X Y : Ω → ℝ) (μ : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, (∑ ω, p ω * X ω * f (X ω)) = μ * ∑ ω, p ω * f (Y ω)

theorem hasDerivAt_finiteLaplace (p X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (finiteLaplace p X)
      (∑ ω, p ω * X ω * Real.exp (t * X ω)) t := by
  have hω : ∀ ω, HasDerivAt (fun s : ℝ => p ω * Real.exp (s * X ω))
      (p ω * X ω * Real.exp (t * X ω)) t := by
    intro ω
    convert (((hasDerivAt_id t).mul_const (X ω)).exp.const_mul (p ω)) using 1 <;>
      simp only [id_eq] <;> ring
  exact HasDerivAt.sum fun ω _ => hω ω

/-- For negative parameters, the bounded size-biased variable reverses the
exponential comparison and bounds the logarithmic derivative from below. -/
theorem finiteLaplace_derivative_lower (p X Y : Ω → ℝ) (μ c t : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hμ : 0 ≤ μ)
    (hsize : FiniteSizeBiasIdentity p X Y μ)
    (hupper : ∀ ω, Y ω ≤ X ω + c) (ht : t ≤ 0) :
    μ * Real.exp (c * t) * finiteLaplace p X t ≤
      ∑ ω, p ω * X ω * Real.exp (t * X ω) := by
  have hsum : (∑ ω, p ω * (Real.exp (c * t) * Real.exp (t * X ω))) ≤
      ∑ ω, p ω * Real.exp (t * Y ω) := by
    apply Finset.sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ (hp ω)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_left (hupper ω) ht
    nlinarith only [hh]
  calc
    _ = μ * ∑ ω, p ω * (Real.exp (c * t) * Real.exp (t * X ω)) := by
      unfold finiteLaplace
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ μ * ∑ ω, p ω * Real.exp (t * Y ω) := mul_le_mul_of_nonneg_left hsum hμ
    _ = _ := (hsize (fun x => Real.exp (t * x))).symm

/-- A finite real size-bias coupling with Y <= X+c gives the exact
negative-parameter Laplace bound. No probability library is needed. -/
theorem finiteLaplace_le_of_bounded_size_bias (p X Y : Ω → ℝ) (μ c : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp_one : ∑ ω, p ω = 1)
    (hμ : 0 ≤ μ) (hc : 0 < c)
    (hsize : FiniteSizeBiasIdentity p X Y μ)
    (hupper : ∀ ω, Y ω ≤ X ω + c) (t : ℝ) (ht : t ≤ 0) :
    finiteLaplace p X t ≤ Real.exp ((μ / c) * (Real.exp (c * t) - 1)) := by
  let G : ℝ → ℝ := fun s =>
    Real.exp (-(μ / c) * Real.exp (c * s)) * finiteLaplace p X s
  have hG : ∀ s : ℝ, HasDerivAt G
      (Real.exp (-(μ / c) * Real.exp (c * s)) *
        ((∑ ω, p ω * X ω * Real.exp (s * X ω)) -
          μ * Real.exp (c * s) * finiteLaplace p X s)) s := by
    intro s
    have hcexp : HasDerivAt (fun u : ℝ => Real.exp (c * u))
        (c * Real.exp (c * s)) s := by
      convert ((hasDerivAt_id s).const_mul c).exp using 1 <;> simp only [id_eq] <;> ring
    have hinner : HasDerivAt (fun u : ℝ => -(μ / c) * Real.exp (c * u))
        (-μ * Real.exp (c * s)) s := by
      convert hcexp.const_mul (-(μ / c)) using 1
      field_simp [hc.ne']
      <;> ring
    convert hinner.exp.mul (hasDerivAt_finiteLaplace p X s) using 1 <;> ring
  have hmono : MonotoneOn G (Set.Iic 0) := by
    apply (convex_Iic (0 : ℝ)).monotoneOn_of_deriv_nonneg
    · intro s _
      exact (hG s).continuousAt.continuousWithinAt
    · intro s _
      exact (hG s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hG s).deriv]
      apply mul_nonneg (Real.exp_nonneg _)
      apply sub_nonneg.mpr
      exact finiteLaplace_derivative_lower p X Y μ c s hp hμ hsize hupper
        (Set.mem_Iic.mp (interior_subset hs))
  have hzero : finiteLaplace p X 0 = 1 := by
    simpa only [finiteLaplace, zero_mul, Real.exp_zero, mul_one] using hp_one
  have hcomp : Real.exp (-(μ / c) * Real.exp (c * t)) * finiteLaplace p X t ≤
      Real.exp (-(μ / c)) := by
    have hh := hmono (show t ∈ Set.Iic 0 by simpa using ht)
      (show (0 : ℝ) ∈ Set.Iic 0 by simp) ht
    simpa only [G, mul_zero, Real.exp_zero, mul_one, hzero] using hh
  apply (mul_le_mul_left (Real.exp_pos (-(μ / c) * Real.exp (c * t)))).mp
  calc
    _ ≤ Real.exp (-(μ / c)) := hcomp
    _ = Real.exp (-(μ / c) * Real.exp (c * t)) *
        Real.exp ((μ / c) * (Real.exp (c * t) - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Natural counts turn the Laplace estimate at log(theta) into the exact
geometric moment bound used for disjoint random position pairs. -/
theorem finite_geometric_le_of_size_bias_three
    (p : Ω → ℝ) (X : Ω → ℕ) (Y : Ω → ℝ) (μ θ : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp_one : ∑ ω, p ω = 1) (hμ : 0 ≤ μ)
    (hsize : FiniteSizeBiasIdentity p (fun ω => (X ω : ℝ)) Y μ)
    (hupper : ∀ ω, Y ω ≤ (X ω : ℝ) + 3)
    (hθpos : 0 < θ) (hθone : θ ≤ 1) :
    (∑ ω, p ω * θ ^ X ω) ≤ Real.exp (-μ * (1 - θ ^ 3) / 3) := by
  have hh := finiteLaplace_le_of_bounded_size_bias p (fun ω => (X ω : ℝ)) Y μ 3
    hp hp_one hμ (by norm_num) hsize hupper (Real.log θ)
    (Real.log_nonpos hθpos.le hθone)
  have hpow : ∀ k : ℕ, Real.exp (Real.log θ * (k : ℝ)) = θ ^ k := by
    intro k
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log hθpos]
  have hcube : Real.exp (3 * Real.log θ) = θ ^ 3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hθpos] using Real.exp_nat_mul (Real.log θ) 3
  unfold finiteLaplace at hh
  simp_rw [hpow] at hh
  rw [hcube] at hh
  convert hh using 1
  congr 1
  ring

end MaxCaterpillar.Frontier.RandomRestriction
