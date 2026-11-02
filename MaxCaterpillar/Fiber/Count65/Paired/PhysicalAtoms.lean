import MaxCaterpillar.Fiber.Count65.Paired.Recession
import MaxCaterpillar.Frontier.Constructions

/-!
# Actual-network bridge for paired first hidden layers

The first hidden layer has two comparison functions and two signed code pairs.
Every second-layer weight and output weight is arbitrary. The all-input network
identity, rather than a presumed recession pattern, supplies the atom balance.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier

variable {m : ℕ}

/-- A normalized paired first hidden layer, with an arbitrary anchor code. -/
def pairedRows (U : Fin 2 → Fin 2 → ℝ) : Fin 6 → Point 4 :=
  ![![1,-1,0,0], ![0,0,1,-1],
    ![0,U 0 0,0,U 0 1], ![0,-U 0 0,0,-U 0 1],
    ![0,U 1 0,0,U 1 1], ![0,-U 1 0,0,-U 1 1]]

private def probe (a b q r : ℝ) : Point 4 := ![a+q,a,b+r,b]

lemma pairedRows_probe (U : Fin 2 → Fin 2 → ℝ) (a b q r : ℝ) (j : Fin 6) :
    (∑ i, pairedRows U j i * probe a b q r i) =
      (![q,r,U 0 0*a+U 0 1*b,-(U 0 0*a+U 0 1*b),
        U 1 0*a+U 1 1*b,-(U 1 0*a+U 1 1*b)] : Fin 6 → ℝ) j := by
  fin_cases j <;> simp [pairedRows, probe, Fin.sum_univ_succ] <;> ring

lemma pairedRows_activation_probe (U : Fin 2 → Fin 2 → ℝ)
    (a b q r : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r) (j : Fin 6) :
    relu (∑ i, pairedRows U j i * probe a b q r i) =
      (![q,r,relu (U 0 0*a+U 0 1*b),relu (-(U 0 0*a+U 0 1*b)),
        relu (U 1 0*a+U 1 1*b),relu (-(U 1 0*a+U 1 1*b))] : Fin 6 → ℝ) j := by
  rw [pairedRows_probe]
  fin_cases j <;> simp [relu_of_nonneg hq, relu_of_nonneg hr]

/-- The anchor-dependent term in each physical second preactivation. -/
noncomputable def codeIntercept (W : Fin m → Fin 6 → ℝ)
    (U : Fin 2 → Fin 2 → ℝ) (a b : ℝ) : Fin m → ℝ := fun k =>
  W k 2*relu (U 0 0*a+U 0 1*b) + W k 3*relu (-(U 0 0*a+U 0 1*b)) +
    W k 4*relu (U 1 0*a+U 1 1*b) + W k 5*relu (-(U 1 0*a+U 1 1*b))

/-- Independent nonnegative increments are actual inputs of every such
network. No assumption on the second-layer activation pattern is made. -/
theorem network_two_increment_identity (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁ = pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (a b : ℝ) :
    ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a+q) (b+r) = ∑ k, net.w₃ k*
        relu (codeIntercept net.W₂ U a b k+net.W₂ k 0*q+net.W₂ k 1*r) := by
  rcases hb with ⟨hb₁,hb₂,hb₃⟩
  intro q r hq hr
  have hh := hnet (probe a b q r)
  have hmax : Maximum 4 (probe a b q r) = max (a+q) (b+r) := by
    rw [Maximum_four]
    change max (max (a+q) a) (max (b+r) b) = max (a+q) (b+r)
    rw [max_eq_left (show a ≤ a+q by linarith only [hq]),
      max_eq_left (show b ≤ b+r by linarith only [hr])]
  rw [Network.eval, hU, hb₁, hb₂, hb₃] at hh
  simp only [Pi.zero_apply, add_zero, pairedRows_activation_probe U a b q r hq hr] at hh
  have hform : ∀ k, (∑ j, net.W₂ k j*
      (![q,r,relu (U 0 0*a+U 0 1*b),relu (-(U 0 0*a+U 0 1*b)),
        relu (U 1 0*a+U 1 1*b),relu (-(U 1 0*a+U 1 1*b))] : Fin 6 → ℝ) j) =
        codeIntercept net.W₂ U a b k+net.W₂ k 0*q+net.W₂ k 1*r := by
    intro k
    simp only [codeIntercept, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
    norm_num [Fin.succ, Fin.ofNat, Fin.ofNat']
    simp only [show (⟨2, by decide⟩ : Fin 6) = 2 from rfl,
      show (⟨3, by decide⟩ : Fin 6) = 3 from rfl,
      show (⟨4, by decide⟩ : Fin 6) = 4 from rfl,
      show (⟨5, by decide⟩ : Fin 6) = 5 from rfl]
    ring
  simp_rw [hform] at hh
  rw [hmax] at hh
  exact hh.symm

/-- The exact finite atom conditions follow from an actual paired network. -/
theorem network_atomBalance (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁ = pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (a b : ℝ) :
    Paired65.AtomBalance
      (fun k => (if net.W₂ k 0+net.W₂ k 1=0 then net.w₃ k else 0)*|net.W₂ k 0|)
      (fun k => -(codeIntercept net.W₂ U a b k+net.W₂ k 0*(b-a))/net.W₂ k 0) :=
  atomBalance_of_two_increment_max a b net.w₃ (codeIntercept net.W₂ U a b)
    (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)
    (network_two_increment_identity net U hU hb hnet a b)

/-- At width five, the actual network supplies at most four active atoms. -/
theorem network_activeAtoms_card (net : Network 4 6 m) (hm : m ≤ 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁ = pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x, net.eval x = Maximum 4 x) :
    (activeAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)).card ≤ 4 :=
  activeAtoms_card_le_four 0 0 net.w₃ (codeIntercept net.W₂ U 0 0)
    (fun k => net.W₂ k 0) (fun k => net.W₂ k 1) hm
    (network_two_increment_identity net U hU hb hnet 0 0)

end MaxCaterpillar.Fiber.Count65.Paired
