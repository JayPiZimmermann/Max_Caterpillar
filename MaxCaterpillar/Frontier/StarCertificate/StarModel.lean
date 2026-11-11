import MaxCaterpillar.Frontier.StarCertificate.XiTargets
import MaxCaterpillar.Frontier.StarCertificate.StarModelProofs

/-! # The certificate's chain vectors are the actual star set-function values -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- A star set function with centre 4 and arbitrary real leaf slopes. -/
noncomputable def starSetFunction (v v' : Fin 4 → ℝ) (B : Finset (Fin 5)) : ℝ :=
  if (4 : Fin 5) ∈ B then
    -(∑ i : Fin 4, if i.castSucc ∉ B then v' i else 0)
  else ∑ i : Fin 4, if i.castSucc ∈ B then v i else 0

noncomputable def starChain (v v' : Fin 4 → ℝ) (p : Fin 120) : Fin 4 → ℝ :=
  fun r => starSetFunction v v' (chamberPrefix p r)

theorem starChain_linear (v v' : Fin 4 → ℝ) (p : Fin 120) (r : Fin 4) :
    starChain v v' p r =
      evalForm (starVCoefficient p r) v + evalForm (starVPrimeCoefficient p r) v' := by
  unfold starChain starSetFunction starVCoefficient starVPrimeCoefficient evalForm
  by_cases hc : (4 : Fin 5) ∈ chamberPrefix p r
  · simp only [if_pos hc, Rat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.castSucc ∈ chamberPrefix p r <;> simp [hi]
  · simp only [if_neg hc, Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.castSucc ∈ chamberPrefix p r <;> simp [hi]

/-- Each dictionary chain is the chain of the actual real-slope star set
function, not a surrogate parameterization. -/
theorem starChain_eq_maskedGamma (v v' : Fin 4 → ℝ) (p : Fin 120) :
    starChain v v' p = maskedGamma 15 p (mixed (maskSet (centerBeforeMask p)) v v') := by
  funext r
  rw [starChain_linear]
  simp only [evalForm, maskedGamma, mixed]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [starVCoefficient_coupling, starVPrimeCoefficient_coupling]
  by_cases hi : i ∈ maskSet (centerBeforeMask p) <;> simp [hi]

/-- Grouping chambers by the leaves before the centre yields exactly the
anchored-ANOVA expression. -/
theorem sum_starPsi_eq_sum_starXi (v v' : Fin 4 → ℝ) :
    (∑ P in (Finset.univ : Finset (Fin 4)).powerset, starPsi P (mixed P v v')) =
      ∑ p : Fin 120, starXi (starChain v v' p) := by
  unfold starPsi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single (maskSet (centerBeforeMask p))]
  · simp only [setMask_maskSet, if_true]
    rw [starChain_eq_maskedGamma]
  · intro P _ hP
    have hn : centerBeforeMask p ≠ setMask P := by
      intro he
      apply hP
      have hh := congrArg maskSet he
      simpa only [maskSet_setMask] using hh.symm
    simp only [if_neg hn]
  · intro hn
    exact False.elim (hn (by simp))

/-- Once the finite coefficient checker is attached, the actual real-slope
star dictionary obeys the required Xi identity. -/
theorem star_sum_of_coefficients
    (hcoeff : ∀ (z : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0)
    (v v' : Fin 4 → ℝ) :
    (∑ p : Fin 120, starXi (starChain v v' p)) = 0 := by
  rw [← sum_starPsi_eq_sum_starXi]
  exact star_anova_sum_of_coefficients hcoeff v v'

end MaxCaterpillar.Frontier.StarCertificate
