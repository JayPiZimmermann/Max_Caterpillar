import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.Realization

/-! # Dominance under one lower change or one coefficient sign reversal

These are finite-family algebraic helpers. No permutation, prefix, coin action,
or coefficient-magnitude invariance is part of their hypotheses. Both stable
evaluations use the same explicitly supplied real parameter.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap

variable {ι : Type*} {c c' : ι→ℝ} {e : ι→ℕ} {g h : ι}

/-- An arbitrary change at one lower exponent leaves the original dominant
coefficient and dominant index unchanged. The changed zero status is unrestricted. -/
theorem dominant_and_leading_eq_of_change_below (hd : Dominant c e h)
    (hgap : e g<e h) (haway : ∀ i,i≠g→c' i=c i) :
    Dominant c' e h ∧ c' h=c h := by
  classical
  have hhg : h≠g := by
    intro heq
    subst h
    exact (Nat.lt_irrefl _ hgap)
  have hlead := haway h hhg
  refine ⟨⟨?_,?_⟩,hlead⟩
  · rw [hlead]
    exact hd.1
  · intro i hi hih
    by_cases hig : i=g
    · subst i
      exact hgap
    · apply hd.2 i ?_ hih
      rwa [haway i hig] at hi

theorem dominant_of_change_below (hd : Dominant c e h)
    (hgap : e g<e h) (haway : ∀ i,i≠g→c' i=c i) : Dominant c' e h :=
  (dominant_and_leading_eq_of_change_below hd hgap haway).1

/-- Dominance depends on the zero support and exponents, not coefficient sizes. -/
theorem dominant_iff_of_same_zero_status (hzero : ∀ i,c' i=0↔c i=0) :
    Dominant c' e h ↔ Dominant c e h := by
  constructor
  · intro hd
    refine ⟨(not_congr (hzero h)).mp hd.1,?_⟩
    intro i hi hih
    exact hd.2 i ((not_congr (hzero i)).mpr hi) hih
  · intro hd
    refine ⟨(not_congr (hzero h)).mpr hd.1,?_⟩
    intro i hi hih
    exact hd.2 i ((not_congr (hzero i)).mp hi) hih

/-- A sign reversal at one coordinate preserves every coefficient's zero status. -/
theorem single_sign_flip_zero_iff (hflip : c' g = -c g)
    (haway : ∀ i,i≠g→c' i=c i) (i : ι) : c' i=0↔c i=0 := by
  classical
  by_cases hig : i=g
  · subst i
    rw [hflip]
    simp
  · rw [haway i hig]

theorem dominant_iff_of_single_sign_flip (hflip : c' g = -c g)
    (haway : ∀ i,i≠g→c' i=c i) : Dominant c' e h ↔ Dominant c e h :=
  dominant_iff_of_same_zero_status (single_sign_flip_zero_iff hflip haway)

theorem dominant_of_single_sign_flip (hd : Dominant c e h)
    (hflip : c' g = -c g) (haway : ∀ i,i≠g→c' i=c i) : Dominant c' e h :=
  (dominant_iff_of_single_sign_flip hflip haway).mpr hd

/-- The retained dominant coefficient has precisely the expected conditional sign. -/
theorem leading_eq_of_single_sign_flip [DecidableEq ι] (hflip : c' g = -c g)
    (haway : ∀ i,i≠g→c' i=c i) : c' h=if h=g then -c h else c h := by
  by_cases hhg : h=g
  · subst h
    simp only [if_true]
    exact hflip
  · rw [if_neg hhg]
    exact haway h hhg

/-- Arbitrary coordinatewise nonzero real scaling also preserves dominance. -/
theorem dominant_coordinate_scale_iff (s : ι→ℝ) (hs : ∀ i,s i≠0) :
    Dominant (fun i => s i*c i) e h ↔ Dominant c e h := by
  apply dominant_iff_of_same_zero_status
  intro i
  simp only [mul_eq_zero,hs i,false_or]

section Stable
variable [Fintype ι] {T : ℝ}

/-- The stable positive product determines both strict signs exactly. -/
theorem stableEvaluation_sign_iff (hs : StableEvaluation c e T) (hd : Dominant c e h) :
    (0<powerSum c e T↔0<c h) ∧ (powerSum c e T<0↔c h<0) :=
  sign_iff_of_positive_product (hs.2 h hd)

theorem stableEvaluation_ne_zero (hs : StableEvaluation c e T) (hd : Dominant c e h) :
    powerSum c e T≠0 := by
  intro hz
  have hp := hs.2 h hd
  rw [hz,mul_zero] at hp
  exact lt_irrefl _ hp

/-- Stable evaluations have the same zero status whenever all coefficient zero
statuses agree; no dominant witness is needed in the all-zero case. -/
theorem stableEvaluation_zero_iff_of_same_zero_status
    (hs : StableEvaluation c e T) (hs' : StableEvaluation c' e T)
    (hzero : ∀ i,c' i=0↔c i=0) : powerSum c' e T=0↔powerSum c e T=0 := by
  have hall : (∀ i,c' i=0)↔∀ i,c i=0 := by
    constructor
    · intro hc i
      exact (hzero i).mp (hc i)
    · intro hc i
      exact (hzero i).mpr (hc i)
  exact hs'.1.trans (hall.trans hs.1.symm)

/-- Same dominant index and same leading coefficient give the same activation
sign, although every lower coefficient may have a different magnitude. -/
theorem stable_sign_iff_of_common_dominant
    (hs : StableEvaluation c e T) (hs' : StableEvaluation c' e T)
    (hd : Dominant c e h) (hd' : Dominant c' e h) (hlead : c' h=c h) :
    (0<powerSum c' e T↔0<powerSum c e T) ∧
      (powerSum c' e T<0↔powerSum c e T<0) := by
  have hc := stableEvaluation_sign_iff hs hd
  have hc' := stableEvaluation_sign_iff hs' hd'
  rw [hlead] at hc'
  exact ⟨hc'.1.trans hc.1.symm,hc'.2.trans hc.2.symm⟩

/-- The arbitrary-lower-change regime used by a higher dominant gap. -/
theorem stable_sign_unchanged_of_change_below
    (hs : StableEvaluation c e T) (hs' : StableEvaluation c' e T)
    (hd : Dominant c e h) (hgap : e g<e h) (haway : ∀ i,i≠g→c' i=c i) :
    (0<powerSum c' e T↔0<powerSum c e T) ∧
      (powerSum c' e T<0↔powerSum c e T<0) := by
  obtain ⟨hd',hlead⟩ := dominant_and_leading_eq_of_change_below hd hgap haway
  exact stable_sign_iff_of_common_dominant hs hs' hd hd' hlead

/-- A sign flip away from the dominant coordinate leaves both strict signs unchanged. -/
theorem stable_sign_unchanged_of_single_sign_flip
    (hs : StableEvaluation c e T) (hs' : StableEvaluation c' e T)
    (hd : Dominant c e h) (hhg : h≠g) (hflip : c' g = -c g)
    (haway : ∀ i,i≠g→c' i=c i) :
    (0<powerSum c' e T↔0<powerSum c e T) ∧
      (powerSum c' e T<0↔powerSum c e T<0) :=
  stable_sign_iff_of_common_dominant hs hs' hd
    (dominant_of_single_sign_flip hd hflip haway) (haway h hhg)

/-- At the dominant coordinate the activation sign is reversed, with neither
stable value zero. No rationality or coefficient-size assumption is used. -/
theorem stable_sign_reversed_of_single_sign_flip
    (hs : StableEvaluation c e T) (hs' : StableEvaluation c' e T)
    (hd : Dominant c e g) (hflip : c' g = -c g)
    (haway : ∀ i,i≠g→c' i=c i) :
    (0<powerSum c' e T↔powerSum c e T<0) ∧
      (powerSum c' e T<0↔0<powerSum c e T) := by
  have hc := stableEvaluation_sign_iff hs hd
  have hc' := stableEvaluation_sign_iff hs'
    (dominant_of_single_sign_flip hd hflip haway)
  rw [hflip] at hc'
  refine ⟨?_,?_⟩
  · have hp : 0<powerSum c' e T↔c g<0 := by
      simpa only [neg_pos] using hc'.1
    exact hp.trans hc.2.symm
  · have hn : powerSum c' e T<0↔0<c g := by
      simpa only [neg_lt_zero] using hc'.2
    exact hn.trans hc.1.symm

/-- In the dominant-flip regime the strict activation bit is complemented. -/
theorem stable_positive_iff_not_positive_of_single_sign_flip
    (hs : StableEvaluation c e T) (hs' : StableEvaluation c' e T)
    (hd : Dominant c e g) (hflip : c' g = -c g)
    (haway : ∀ i,i≠g→c' i=c i) :
    0<powerSum c' e T↔¬0<powerSum c e T := by
  have hn := stableEvaluation_ne_zero hs hd
  have hneg : powerSum c e T<0↔¬0<powerSum c e T := by
    constructor
    · intro h hp
      linarith only [h,hp]
    · intro h
      exact lt_of_le_of_ne (not_lt.mp h) hn
  exact (stable_sign_reversed_of_single_sign_flip hs hs' hd hflip haway).1.trans hneg

/-- Coefficient zero statuses and the entire stable value's zero status are
both invariant under the same single sign flip. -/
theorem stable_zero_iff_of_single_sign_flip
    (hs : StableEvaluation c e T) (hs' : StableEvaluation c' e T)
    (hflip : c' g = -c g) (haway : ∀ i,i≠g→c' i=c i) :
    powerSum c' e T=0↔powerSum c e T=0 :=
  stableEvaluation_zero_iff_of_same_zero_status hs hs'
    (single_sign_flip_zero_iff hflip haway)
end Stable
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
