import research.sN.clean_quadratic_20261103.ordinary.Bounds

/-! Independent literal-array signatures and an exact nonzero-bias control. -/
set_option autoImplicit false
namespace MaxCaterpillar.CleanQuadratic.Ordinary.Check
open BigOperators

/-- Six unrestricted real arrays, with ordinary sequential evaluation only. -/
theorem exact_explicit_type {N h₁ h₂ : ℕ} [NeZero N] (hN : 3 ≤ N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (θ a : Fin h₂ → ℝ) (β : ℝ)
    (C : ℝ) (hC : 0 < C)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k, a k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i * x i) + b j)) + θ k)) + β
        = Maximum N x)
    (hwidth : (h₁ : ℝ) ≤ C * (N : ℝ)^2) :
    (N : ℝ)^2 / (175000 * max 1 C) ≤ (h₂ : ℝ) :=
  explicit_quadratic hN ⟨A,b,W,θ,a,β⟩ C hC hmax hwidth

/-- The same six-array contract for the absolute existential constant. -/
theorem exact_exists_type :
    ∃ c : ℝ, 0 < c ∧
      ∀ {N h₁ h₂ : ℕ} [NeZero N], 3 ≤ N →
        ∀ (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
          (W : Fin h₂ → Fin h₁ → ℝ) (θ a : Fin h₂ → ℝ) (β C : ℝ),
          0 < C →
          (∀ x : Fin N → ℝ,
            (∑ k, a k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i * x i) + b j)) + θ k)) + β
              = Maximum N x) →
          (h₁ : ℝ) ≤ C * (N : ℝ)^2 →
          c * (N : ℝ)^2 / max 1 C ≤ (h₂ : ℝ) := by
  obtain ⟨c, hc, h⟩ := exists_uniform_quadratic_constant
  refine ⟨c, hc, ?_⟩
  intro N h₁ h₂ _ hN A b W θ a β C hC hmax hwidth
  exact h hN ⟨A,b,W,θ,a,β⟩ C hC hmax hwidth

/-- Fixed-C existential statement, with no skip parameters in the model. -/
theorem exact_fixed_scale_type (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {N h₁ h₂ : ℕ} [NeZero N], 3 ≤ N →
        ∀ (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
          (W : Fin h₂ → Fin h₁ → ℝ) (θ a : Fin h₂ → ℝ) (β : ℝ),
          (∀ x : Fin N → ℝ,
            (∑ k, a k * max 0 ((∑ j, W k j * max 0 ((∑ i, A j i * x i) + b j)) + θ k)) + β
              = Maximum N x) →
          (h₁ : ℝ) ≤ C * (N : ℝ)^2 →
          c * (N : ℝ)^2 ≤ (h₂ : ℝ) := by
  obtain ⟨c, hc, h⟩ := exists_quadratic_constant_for_scale C hC
  refine ⟨c, hc, ?_⟩
  intro N h₁ h₂ _ hN A b W θ a β hmax hwidth
  exact h hN ⟨A,b,W,θ,a,β⟩ hmax hwidth

/-- Add one unused first-hidden neuron with a nonzero bias. -/
def withDormantBias {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) : Network N (h₁+1) h₂ where
  W₁ := Fin.cases (fun _ => 0) net.W₁
  b₁ := Fin.cases 1 net.b₁
  W₂ k := Fin.cases 0 (net.W₂ k)
  b₂ := net.b₂
  w₃ := net.w₃
  b₃ := net.b₃

theorem withDormantBias_eval {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) (x : Point N) :
    (withDormantBias net).eval x = net.eval x := by
  simp only [Network.eval,withDormantBias,Fin.sum_univ_succ,Fin.cases_zero,
    Fin.cases_succ,zero_mul,zero_add]

/-- At the smallest advertised arity, the C=1 hypotheses are satisfiable
by an actual network with a nonzero first-hidden-layer bias. -/
theorem actual_biased_max_three :
    ∃ net : Network 3 (firstWidth 3+1) (secondWidth 3),
      (∀ x, net.eval x = Maximum 3 x) ∧
      ((firstWidth 3+1 : ℕ) : ℝ) ≤ (3 : ℝ)^2 ∧
      net.b₁ 0 = 1 ∧
      (3 : ℝ)^2 / 175000 ≤ (secondWidth 3 : ℝ) := by
  obtain ⟨net,hnet,_hrational,_hzeroBias⟩ := caterpillar_net 3
  have hmax : ∀ x, (withDormantBias net).eval x = Maximum 3 x :=
    fun x => (withDormantBias_eval net x).trans (hnet x)
  have hwidthNat : firstWidth 3+1 ≤ 9 := by decide
  have hwidth : ((firstWidth 3+1 : ℕ) : ℝ) ≤ (3 : ℝ)^2 := by
    rw [show (3 : ℝ)^2 = 9 by norm_num]
    exact_mod_cast hwidthNat
  refine ⟨withDormantBias net,hmax,hwidth,rfl,?_⟩
  simpa only [mul_one] using
    explicit_quadratic_ge_one (by decide : 3 ≤ 3) (withDormantBias net) 1 le_rfl hmax
      (by simpa only [one_mul] using hwidth)

#check @exact_explicit_type
#check @exact_exists_type
#check @exact_fixed_scale_type
#print axioms exact_explicit_type
#print axioms exact_exists_type
#print axioms exact_fixed_scale_type
#print axioms withDormantBias_eval
#print axioms actual_biased_max_three
end MaxCaterpillar.CleanQuadratic.Ordinary.Check
