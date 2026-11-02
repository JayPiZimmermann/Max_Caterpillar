import MaxCaterpillar.Frontier.StarCertificate.XiTargets
import MaxCaterpillar.Frontier.StarCertificate.Checker.FastInteger
import MaxCaterpillar.Frontier.StarCertificate.XiFastSelectors
import MaxCaterpillar.Frontier.StarCertificate.XiFastKappa
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- Assemble the eighty anchored coefficient vectors from one shared table
of the 256 masked chamber-group sums. -/
def collectAnovaCoefficients (psi : Fin 16 → Fin 16 → IntegerForm 4)
    (t : Fin 80) : IntegerForm 4 :=
  let S := maskSet (pairS t)
  let A := maskSet (pairA t)
  fun i => ∑ T in S.powerset, (-1 : ℤ) ^ (S \ T).card *
    ∑ P in (Finset.univ : Finset (Fin 4)).powerset.filter (fun P => P ∩ S = A),
      psi (setMask T) (setMask P) i

theorem starAnovaIntegerCoefficients_collect (s : Fin 15 → Sign) :
    starAnovaIntegerCoefficients s =
      collectAnovaCoefficients (fun T P => maskedPsiIntegerCoefficients T P s) := rfl

theorem starAnovaIntegerCoefficients_of_shared_table (s : Fin 15 → Sign)
    (psi : Fin 16 → Fin 16 → IntegerForm 4)
    (hpsi : ∀ T P i, maskedPsiIntegerCoefficients T P s i = psi T P i) :
    starAnovaIntegerCoefficients s = collectAnovaCoefficients psi := by
  funext t i
  unfold starAnovaIntegerCoefficients componentIntegerCoefficients collectAnovaCoefficients
  simp only [hpsi]

end MaxCaterpillar.Frontier.StarCertificate

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def fastMaskedXiIntegerCoefficients (T : Fin 16) (p : Fin 120) (s : Fin 15 → Sign) :
    IntegerForm 4 :=
  let chainSigns := fun j => (fastMaskedChain T p j).sign s
  let orientation := headSign chainSigns
  let normalized := fun t => normalizeSign orientation ((fastMaskedCoarse T p t).sign s)
  let weights := if fastMixed chainSigns = true then fastStarIntegerKappa normalized else starIntegerOmega
  fun i => intSum 4 (fun j => (orientation.integerDirection * weights j) *
    (fastMaskedChain T p j).integerForm starIntegerSubsetForms i)

theorem fastMaskedXiIntegerCoefficients_eq (T : Fin 16) (p : Fin 120)
    (s : Fin 15 → Sign) (i : Fin 4) :
    fastMaskedXiIntegerCoefficients T p s i = maskedXiIntegerCoefficients T p s i := by
  unfold fastMaskedXiIntegerCoefficients maskedXiIntegerCoefficients
  simp only [fastMaskedChain_eq, fastMaskedCoarse_eq, fastMixed_eq_true, fastStarIntegerKappa_eq]
  exact intSum_eq_sum 4 _

def fastMaskedPsiIntegerCoefficients (T P : Fin 16) (s : Fin 15 → Sign) : IntegerForm 4 :=
  fun i => intSum 120 (fun p =>
    if fastCenterBeforeMask p = P then fastMaskedXiIntegerCoefficients T p s i else 0)

theorem fastMaskedPsiIntegerCoefficients_eq (T P : Fin 16) (s : Fin 15 → Sign) (i : Fin 4) :
    fastMaskedPsiIntegerCoefficients T P s i = maskedPsiIntegerCoefficients T P s i := by
  unfold fastMaskedPsiIntegerCoefficients maskedPsiIntegerCoefficients
  simp only [fastCenterBeforeMask_eq]
  rw [intSum_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : centerBeforeMask p = P
  · simp only [if_pos hp, fastMaskedXiIntegerCoefficients_eq]
  · simp only [if_neg hp]

def integerTable3Check {a b c : ℕ} (f g : Fin a → Fin b → Fin c → ℤ) : Bool :=
  finAll a (fun i => finAll b (fun j => finAll c (fun k => decide (f i j k = g i j k))))

theorem integerTable3Check_sound {a b c : ℕ} (f g : Fin a → Fin b → Fin c → ℤ)
    (h : integerTable3Check f g = true) : ∀ i j k, f i j k = g i j k := by
  intro i j k
  have hi := (finAll_eq_true a _).mp h i
  have hj := (finAll_eq_true b _).mp hi j
  exact of_decide_eq_true ((finAll_eq_true c _).mp hj k)

def integerTable2Check {a b : ℕ} (f g : Fin a → Fin b → ℤ) : Bool :=
  finAll a (fun i => finAll b (fun j => decide (f i j = g i j)))

theorem integerTable2Check_sound {a b : ℕ} (f g : Fin a → Fin b → ℤ)
    (h : integerTable2Check f g = true) : ∀ i j, f i j = g i j := by
  intro i j
  have hi := (finAll_eq_true a _).mp h i
  exact of_decide_eq_true ((finAll_eq_true b _).mp hi j)

end MaxCaterpillar.Frontier.StarCertificate
