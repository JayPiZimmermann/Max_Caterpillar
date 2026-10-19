import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Interval

/-! # The mathematical definitions

`Network N h₁ h₂` consists of the six arrays of real parameters in an
ordinary two-hidden-layer ReLU network. Its function is the explicit formula
`Network.eval` below. The widths are type parameters, the output is affine,
and there are no skip connections. All equalities concern every real input.
-/

namespace MaxCaterpillar

open BigOperators

abbrev Point (N : ℕ) := Fin N → ℝ

/-- The scalar ReLU function, also used componentwise in the network. -/
noncomputable def relu (t : ℝ) : ℝ := max 0 t

/-- The parameters of a scalar network with two hidden layers. Matrix rows
index output neurons and columns index inputs to that layer. -/
structure Network (N h₁ h₂ : ℕ) where
  W₁ : Fin h₁ → Fin N → ℝ
  b₁ : Fin h₁ → ℝ
  W₂ : Fin h₂ → Fin h₁ → ℝ
  b₂ : Fin h₂ → ℝ
  w₃ : Fin h₂ → ℝ
  b₃ : ℝ

/-- The function `x ↦ w₃ᵀ σ(W₂ σ(W₁ x + b₁) + b₂) + b₃`. -/
noncomputable def Network.eval {N h₁ h₂ : ℕ} (net : Network N h₁ h₂)
    (x : Point N) : ℝ :=
  (∑ k, net.w₃ k * relu
    ((∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k))
    + net.b₃

/-- The maximum of the `N` input coordinates; defined for positive arity. -/
noncomputable def Maximum (N : ℕ) [NeZero N] (x : Point N) : ℝ :=
  Finset.univ.sup'
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, Finset.mem_univ _⟩ x

def firstWidth (N : ℕ) : ℕ := N.choose 2 + N + 1

/-- The paper's count `C_N = ∑_{m=2}^{N-1} C(N,m) (m!/2) (N-m) m^(N-m-1)`: for a
spine with `m` vertices, choose its vertex set, its order up to reversal, its
apex, and the attachment of each of its `N - m - 1` leaves. -/
def coneCount (N : ℕ) : ℕ :=
  ∑ m in Finset.Icc 2 (N - 1), N.choose m * (m.factorial / 2) * (N - m) * m ^ (N - m - 1)

/-- The paper's second width `3^(N-2) C_N - N(N-1) + 2`: all face descriptions
of the cones, minus the absorbed pair hinges, plus two remainder units. -/
def secondWidth (N : ℕ) : ℕ :=
  coneCount N * 3 ^ (N - 2) - N * (N - 1) + 2

end MaxCaterpillar
