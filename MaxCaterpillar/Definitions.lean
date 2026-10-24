import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.LinearAlgebra.FiniteDimensional
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Normalize
import MaxNN.Constructions.MaxN.Width.Layer.Features

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

/-- All weight entries `W₁`, `W₂`, `w₃` are rational. -/
def Network.HasRationalWeights {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) : Prop :=
  (∀ j i, ∃ q : ℚ, (q : ℝ) = net.W₁ j i) ∧ (∀ k j, ∃ q : ℚ, (q : ℝ) = net.W₂ k j) ∧
    ∀ k, ∃ q : ℚ, (q : ℝ) = net.w₃ k

/-- All three bias arrays vanish. -/
def Network.HasZeroBiases {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) : Prop :=
  net.b₁ = 0 ∧ net.b₂ = 0 ∧ net.b₃ = 0

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

/-! ## Caterpillar functions and caterpillar expansions

For `N = r + 2` inputs, a caterpillar face description `k = (h, M)` gives the
caterpillar function `U_k(x) = σ(h(x) + Σ_{ℓ ∈ M} σ(ℓ(x)))`, where the head `h`
and the labels `ℓ` are differences `x_i - x_j` of coordinates along a
caterpillar tree (stored in reduced coordinates). The auxiliary functions are
the first-hidden-layer features `σ(x_i)`, `σ(-x_i)`, `σ(x_i - x_j)`. -/

/-- A caterpillar face description for `N = r + 2` inputs. -/
abbrev FaceKey (r : ℕ) := MaxNN.Caterpillar.Corrections.RealKey (r + 1)

/-- The finite set `𝒦₀` of normalized caterpillar face descriptions. -/
noncomputable def caterpillarDescriptions (r : ℕ) : Finset (FaceKey r) :=
  MaxNN.Caterpillar.Corrections.normalizedKeys r

/-- The caterpillar function `U_k(x) = σ(h(x) + Σ_{ℓ ∈ M} σ(ℓ(x)))` of `k = (h, M)`. -/
noncomputable def caterpillarFunction {r : ℕ} (k : FaceKey r) : Point (r + 1 + 1) → ℝ :=
  MaxNN.Caterpillar.Corrections.realUnitY k

/-- The auxiliary functions `σ(x_i)`, `σ(-x_i)` and `σ(x_i - x_j)` (`i < j`). -/
noncomputable def auxiliaryFunction (N : ℕ) (j : Fin (MaxNN.Width.W N)) : Point N → ℝ :=
  fun x => MaxNN.Width.feat N x j

/-- `K` is a caterpillar expansion of the maximum: `K ⊆ 𝒦₀` and
`max_N = Σ_{k ∈ K} d_k U_k + Σ_j a_j (auxiliary function j)` on all of `ℝ^N`
for some real coefficients `d` and `a`. Its size `K.card` is the number of
second-hidden-layer neurons spent on caterpillar functions. -/
def IsCaterpillarExpansion (r : ℕ) (K : Finset (FaceKey r)) : Prop :=
  K ⊆ caterpillarDescriptions r ∧
    ∃ (d : FaceKey r → ℝ) (a : Fin (MaxNN.Width.W (r + 1 + 1)) → ℝ),
      ∀ x, Maximum (r + 1 + 1) x =
        ∑ k in K, d k * caterpillarFunction k x + ∑ j, a j * auxiliaryFunction (r + 1 + 1) j x

/-- The auxiliary span `A_N`. -/
noncomputable def auxiliarySpan (N : ℕ) : Submodule ℝ (Point N → ℝ) :=
  Submodule.span ℝ (Set.range (auxiliaryFunction N))

/-- The caterpillar span `V_N`: all caterpillar functions and auxiliary functions. -/
noncomputable def caterpillarSpan (r : ℕ) : Submodule ℝ (Point (r + 1 + 1) → ℝ) :=
  Submodule.span ℝ ((caterpillarFunction '' ↑(caterpillarDescriptions r)) ∪
    Set.range (auxiliaryFunction (r + 1 + 1)))

/-- `q_N = dim(V_N / A_N)`: the dimension of the caterpillar span modulo the
auxiliary functions. -/
noncomputable def caterpillarDim (r : ℕ) : ℕ :=
  FiniteDimensional.finrank ℝ (↥(caterpillarSpan r) ⧸
    (auxiliarySpan (r + 1 + 1)).comap (caterpillarSpan r).subtype)

end MaxCaterpillar
