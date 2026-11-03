import research.sN.overnight_20261103.portfolio.coordinate_quotient.Section
import research.sN.overnight_20261103.portfolio.coordinate_quotient.Bounds

/-! Independent raw-array contract and controls for coordinate identification. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.CoordinateQuotient.Check
open BigOperators Frontier Frontier.RandomRestriction AffineSkipExtension

theorem exact_raw_eval {N m h₁ h₂ : ℕ}
    (A : Fin h₁ → Point N) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Point N)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Point N) (β : ℝ)
    (φ : Fin N → Fin m) (x : Point m) :
    (∑ k, d k * relu ((∑ j, W k j *
      relu ((∑ c, (∑ i, if φ i = c then A j i else 0) * x c) + b j)) +
      (∑ c, (∑ i, if φ i = c then U k i else 0) * x c) + θ k)) +
      ((∑ j, B j * relu ((∑ c, (∑ i, if φ i = c then A j i else 0) * x c) + b j)) +
        (∑ c, (∑ i, if φ i = c then L i else 0) * x c) + β) =
    (∑ k, d k * relu ((∑ j, W k j *
      relu ((∑ i, A j i * x (φ i)) + b j)) +
      (∑ i, U k i * x (φ i)) + θ k)) +
      ((∑ j, B j * relu ((∑ i, A j i * x (φ i)) + b j)) +
        (∑ i, L i * x (φ i)) + β) := by
  exact eval_quotient ⟨A,b,W,U,θ,d,B,L,β⟩ φ x

theorem exact_quadratic {N m h₁ h₂ : ℕ} [NeZero N] [NeZero m]
    (hm : 3 ≤ m) (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, eval net x = Maximum N x)
    (φ : Fin N → Fin m) (hφ : Function.Surjective φ)
    (hrows : ∀ j, net.b j = 0 → (∑ i, net.A j i) = 0 →
      ((Finset.univ : Finset (Fin m)).filter
        (fun c => (∑ i, if φ i = c then net.A j i else 0) ≠ 0)).card ≤ 2) :
    (m:ℝ)^2 / 3000000 ≤ (h₂:ℝ) := by
  exact affine_quotient_quadratic hm net hnet φ hφ hrows

def maxTwo : AffineSkipNetwork 2 1 0 where
  A _ i := if i = 0 then 1 else -1
  b := 0
  W := 0
  U := 0
  θ := 0
  d := 0
  B := fun _ => 1
  L i := if i = 1 then 1 else 0
  β := 0

theorem maxTwo_eval (x : Point 2) : eval maxTwo x = Maximum 2 x := by
  have he : eval maxTwo x = relu (x 0-x 1)+x 1 := by
    norm_num [eval, outputSkip, first, maxTwo, Fin.sum_univ_two,
      Fin.sum_univ_one, sub_eq_add_neg]
  rw [he]
  rcases le_total (x 1) (x 0) with h | h
  · have hm : Maximum 2 x = x 0 :=
      Maximum_eq_of x (x 0) 0 rfl (by intro i; fin_cases i <;> simp_all)
    rw [hm, relu, max_eq_right (sub_nonneg.mpr h)]
    ring
  · have hm : Maximum 2 x = x 1 :=
      Maximum_eq_of x (x 1) 1 rfl (by intro i; fin_cases i <;> simp_all)
    rw [hm, relu, max_eq_left (sub_nonpos.mpr h)]
    ring

/-- A noninjective surjection really preserves an exact network. -/
theorem noninjective_surjection_control (x : Point 1) :
    eval (quotient maxTwo (fun _ => (0 : Fin 1))) x = Maximum 1 x := by
  apply quotient_computes_max maxTwo maxTwo_eval
  intro b
  exact ⟨0, by fin_cases b; rfl⟩

/-- Surjectivity is necessary: a missing coordinate can carry the maximum. -/
theorem nonsurjection_control :
    Maximum 2 (pullback (fun _ : Fin 2 => (0 : Fin 2))
      (fun i : Fin 2 => if i = 0 then 0 else 1)) ≠
    Maximum 2 (fun i : Fin 2 => if i = 0 then 0 else 1) := by
  have hleft : Maximum 2 (pullback (fun _ : Fin 2 => (0 : Fin 2))
      (fun i : Fin 2 => if i = 0 then 0 else 1)) = 0 := by
    convert Maximum_zero (N:=2) using 1
  have hright : Maximum 2 (fun i : Fin 2 => if i = 0 then 0 else 1) = 1 := by
    apply Maximum_eq_of _ 1 1
    · norm_num
    · intro i
      split_ifs <;> norm_num
  rw [hleft, hright]
  norm_num

#check @exact_raw_eval
#check @exact_quadratic
#print axioms exact_raw_eval
#print axioms exact_quadratic
#print axioms maxTwo_eval
#print axioms noninjective_surjection_control
#print axioms nonsurjection_control
end MaxCaterpillar.Overnight.CoordinateQuotient.Check
