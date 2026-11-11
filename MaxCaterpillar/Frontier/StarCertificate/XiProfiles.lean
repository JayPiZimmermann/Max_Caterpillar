import MaxCaterpillar.Frontier.StarCertificate.XiInteger
import MaxCaterpillar.Frontier.StarCertificate.XiFastSelectors
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def restrictPattern (T : Fin 16) (s : Fin 15 → Sign) (j : Fin 15) : Sign :=
  if Nat.land (j.val + 1) T.val = j.val + 1 then s j else .zero

def FormRef.Supported (T : Fin 16) : FormRef 15 → Prop
  | .zero => True
  | .pos j => Nat.land (j.val + 1) T.val = j.val + 1
  | .neg j => Nat.land (j.val + 1) T.val = j.val + 1

instance supportedDecidable (T : Fin 16) (r : FormRef 15) : Decidable (r.Supported T) := by
  cases r <;> unfold FormRef.Supported <;> infer_instance

theorem maskRef_supported : ∀ (T M : Fin 16) (negative : Bool),
    (maskRef negative (Nat.land T.val M.val)).Supported T := by decide

theorem fastChainMask_lt : ∀ (p : Fin 120) (j : Fin 4), fastChainMask p j < 16 := by decide

theorem fastCoarseMask_lt : ∀ (p : Fin 120) (j : Fin 10), fastCoarseMask p j < 16 := by decide

theorem maskedChain_supported (T : Fin 16) (p : Fin 120) (j : Fin 4) :
    (maskedChain T p j).Supported T := by
  rw [← fastMaskedChain_eq]
  exact maskRef_supported T ⟨fastChainMask p j,fastChainMask_lt p j⟩ (fastChainNegative p j)

theorem maskedCoarse_supported (T : Fin 16) (p : Fin 120) (j : Fin 10) :
    (maskedCoarse T p j).Supported T := by
  rw [← fastMaskedCoarse_eq]
  exact maskRef_supported T ⟨fastCoarseMask p j,fastCoarseMask_lt p j⟩ (fastCoarseNegative p j)

theorem FormRef.sign_restrict (r : FormRef 15) (T : Fin 16) (s : Fin 15 → Sign)
    (hr : r.Supported T) : r.sign (restrictPattern T s) = r.sign s := by
  cases r with
  | zero => rfl
  | pos j =>
    change Nat.land (j.val + 1) T.val = j.val + 1 at hr
    simp only [FormRef.sign, restrictPattern, if_pos hr]
  | neg j =>
    change Nat.land (j.val + 1) T.val = j.val + 1 at hr
    simp only [FormRef.sign, restrictPattern, if_pos hr]

/-- A masked chamber only reads signs of subsets contained in its mask.
This permits sharing the same checked profile across different resonance faces. -/
theorem maskedXiIntegerCoefficients_restrict (T : Fin 16) (p : Fin 120)
    (s : Fin 15 → Sign) :
    maskedXiIntegerCoefficients T p (restrictPattern T s) = maskedXiIntegerCoefficients T p s := by
  have hc : (fun j => (maskedChain T p j).sign (restrictPattern T s)) =
      fun j => (maskedChain T p j).sign s := by
    funext j
    exact FormRef.sign_restrict _ T s (maskedChain_supported T p j)
  have hh : (fun j => (maskedCoarse T p j).sign (restrictPattern T s)) =
      fun j => (maskedCoarse T p j).sign s := by
    funext j
    exact FormRef.sign_restrict _ T s (maskedCoarse_supported T p j)
  unfold maskedXiIntegerCoefficients
  rw [hc]
  have hhh : ∀ j, (maskedCoarse T p j).sign (restrictPattern T s) = (maskedCoarse T p j).sign s :=
    congrFun hh
  simp only [hhh]

theorem maskedPsiIntegerCoefficients_restrict (T P : Fin 16) (s : Fin 15 → Sign) :
    maskedPsiIntegerCoefficients T P (restrictPattern T s) = maskedPsiIntegerCoefficients T P s := by
  funext i
  unfold maskedPsiIntegerCoefficients
  apply Finset.sum_congr rfl
  intro p _
  simp only [maskedXiIntegerCoefficients_restrict]

end MaxCaterpillar.Frontier.StarCertificate

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem FormRef.sign_opposite {m : ℕ} (r : FormRef m) (s : Fin m → Sign) :
    r.sign (fun j => (s j).opposite) = (r.sign s).opposite := by
  cases r <;> rfl

theorem Sign.integerDirection_opposite (s : Sign) :
    s.opposite.integerDirection = -s.integerDirection := by
  cases s <;> rfl

/-- Evenness of Xi appears as oddness of its linear coefficient vectors
under reversal of all resonance signs. -/
theorem maskedXiIntegerCoefficients_opposite (T : Fin 16) (p : Fin 120)
    (s : Fin 15 → Sign) (i : Fin 4) :
    maskedXiIntegerCoefficients T p (fun j => (s j).opposite) i =
      -maskedXiIntegerCoefficients T p s i := by
  have hc : (fun j => (maskedChain T p j).sign (fun k => (s k).opposite)) =
      fun j => ((maskedChain T p j).sign s).opposite := by
    funext j
    exact FormRef.sign_opposite _ s
  unfold maskedXiIntegerCoefficients
  rw [hc]
  simp only [FormRef.sign_opposite, headSign_opposite, mixed_opposite,
    normalize_opposite, Sign.integerDirection_opposite]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem maskedPsiIntegerCoefficients_opposite (T P : Fin 16) (s : Fin 15 → Sign) (i : Fin 4) :
    maskedPsiIntegerCoefficients T P (fun j => (s j).opposite) i =
      -maskedPsiIntegerCoefficients T P s i := by
  unfold maskedPsiIntegerCoefficients
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : centerBeforeMask p = P
  · simp only [if_pos hp, maskedXiIntegerCoefficients_opposite]
  · simp only [if_neg hp, neg_zero]

end MaxCaterpillar.Frontier.StarCertificate

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem componentIntegerCoefficients_opposite (S A : Finset (Fin 4))
    (s : Fin 15 → Sign) (i : Fin 4) :
    componentIntegerCoefficients S A (fun j => (s j).opposite) i =
      -componentIntegerCoefficients S A s i := by
  simp only [componentIntegerCoefficients, maskedPsiIntegerCoefficients_opposite,
    Finset.sum_neg_distrib, mul_neg]

end MaxCaterpillar.Frontier.StarCertificate
