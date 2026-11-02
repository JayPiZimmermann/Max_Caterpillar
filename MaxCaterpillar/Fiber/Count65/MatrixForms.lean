import MaxCaterpillar.Definitions
import MaxCaterpillar.Fiber.Star65.Construction

/-! # First-matrix predicates for the three Max4 component sectors

These are predicates on the actual weight matrix; arbitrary suffix parameters
and biases are unrestricted. Exhaustion is proved in higher modules.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65

/-- A paired code over the two inactive anchors of a perfect matching. -/
noncomputable def pairedRows (a b c d : ℝ) : Fin 6 → Point 4 :=
  ![![1, -1, 0, 0], ![0, 0, 1, -1],
    ![0, a, 0, b], ![0, -a, 0, -b],
    ![0, c, 0, d], ![0, -c, 0, -d]]

/-- The paired sector's first-matrix condition. The two anchor code rows
are independent; zero coordinate sums at canonical walls are allowed. -/
def PairedFirstMatrixForm (net : Network 4 6 5) : Prop :=
  ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧
    ∃ s : Fin 6 → ℝ, (∀ j, 0 < s j) ∧
    ∃ p : Equiv.Perm (Fin 6), ∃ q : Equiv.Perm (Fin 4),
      ∀ j i, net.W₁ j i = s j * pairedRows a b c d (p j) (q i)

/-- The positive-path sector includes its star endpoint, but excludes
its duplicate-row endpoint. No suffix restriction is imposed. -/
def StarFirstMatrixForm (net : Network 4 6 5) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
    ∃ s : Fin 6 → ℝ, (∀ j, 0 < s j) ∧
    ∃ p : Equiv.Perm (Fin 6), ∃ q : Equiv.Perm (Fin 4),
      ∀ j i, net.W₁ j i = s j * Star65.firstRows r (p j) (q i)


end MaxCaterpillar.Fiber.Count65
