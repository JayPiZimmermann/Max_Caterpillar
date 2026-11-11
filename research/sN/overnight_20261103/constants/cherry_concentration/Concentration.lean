import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesProbability

/-! Finite second-moment assembly for actual isolated low-rank gaps.
The moment assumptions here are discharged in the separate Actual module. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.OvernightConstants.CherryConcentration
open BigOperators Frontier.RandomRestriction.GoodEvent
variable {m K : ℕ}

lemma rankAverage_centered_square (K : ℕ) (f : Finset (Fin m) → ℝ) (a : ℝ) :
    rankAverage K (fun Γ => (f Γ-a)^2) =
      rankAverage K (fun Γ => (f Γ)^2) - 2*a*rankAverage K f + a^2 := by
  have hp : (fun Γ => (f Γ-a)^2) = (fun Γ => (f Γ)^2 - 2*a*f Γ + a^2) := by
    funext Γ
    ring
  rw [hp]
  have hc := rankAverage_const (m:=m) K (a^2)
  unfold rankAverage at hc ⊢
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hc]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

/-- A literal finite-event version of the second-moment inequality. -/
lemma event_fraction_mul_square_le (E : Finset (Equiv.Perm (Fin m)))
    (f : Finset (Fin m) → ℝ) (a δ : ℝ) (hδ : 0≤δ)
    (hE : ∀ ρ∈E, a+δ≤f (smallRankGaps ρ K)) :
    ((E.card:ℝ)/Fintype.card (Equiv.Perm (Fin m)))*δ^2 ≤
      rankAverage K (fun Γ => (f Γ-a)^2) := by
  classical
  have hsum : (E.card:ℝ)*δ^2 ≤
      ∑ ρ : Equiv.Perm (Fin m), (f (smallRankGaps ρ K)-a)^2 := by
    calc
      _ = ∑ _ρ in E,δ^2 := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ∑ ρ in E,(f (smallRankGaps ρ K)-a)^2 := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have hd : δ≤f (smallRankGaps ρ K)-a := by linarith only [hE ρ hρ]
        exact pow_le_pow_left hδ hd 2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        (by intro ρ _ _; exact sq_nonneg _)
  unfold rankAverage
  rw [←Finset.mul_sum]
  have hp : 0≤(1:ℝ)/Fintype.card (Equiv.Perm (Fin m)) := by positivity
  have hh := mul_le_mul_of_nonneg_left hsum hp
  convert hh using 1 <;> ring

/-- Bad isolated count is at least K/9 above the center K²/m when K≤m/8. -/
lemma bad_event_gap (hm : 0<m) (hK : 36≤K) (hKm : 8*K≤m)
    (ρ : Equiv.Perm (Fin m)) (hρ : ρ∈badIsolatedEvent m K) :
    (K:ℝ)^2/(m:ℝ)+(K:ℝ)/9 ≤
      ((selectedGapAdjacencies (smallRankGaps ρ K)).card:ℝ) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hKR : (36:ℝ)≤K := by exact_mod_cast hK
  have hKmR : 8*(K:ℝ)≤m := by exact_mod_cast hKm
  have hKle : K≤m := by linarith only [hKm]
  have hc := card_le_isolated_add_one_add_two_adjacent (smallRankGaps ρ K)
  rw [card_smallRankGaps hKle] at hc
  have hcR : (K:ℝ) ≤ ((isolatedGaps (smallRankGaps ρ K)).card:ℝ)+1+
      2*((selectedGapAdjacencies (smallRankGaps ρ K)).card:ℝ) := by exact_mod_cast hc
  have hbad := (mem_badIsolatedEvent ρ).mp hρ
  have hcenter : (K:ℝ)^2/(m:ℝ)≤(K:ℝ)/8 := by
    apply (div_le_iff hmR).mpr
    have hh := mul_le_mul_of_nonneg_left hKmR (Nat.cast_nonneg (α:=ℝ) K)
    nlinarith only [hh]
  linarith only [hcR,hbad,hKR,hcenter]

/-- The actual bad-event fraction is small once its two literal moments are bounded. -/
theorem bad_fraction_le_of_moments (hm : 20000≤m) (hK : 36≤K) (hKm : 8*K≤m)
    (hfirst : rankAverage K (fun Γ : Finset (Fin m) =>
      ((selectedGapAdjacencies Γ).card:ℝ)) = (K:ℝ)*((K:ℝ)-1)/(m:ℝ))
    (hsecond : rankAverage K (fun Γ : Finset (Fin m) =>
      ((selectedGapAdjacencies Γ).card:ℝ)^2) ≤
      (K:ℝ)^4/(m:ℝ)^2+4*(K:ℝ)^3/(m:ℝ)^2+(K:ℝ)^2/(m:ℝ)) :
    ((badIsolatedEvent m K).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)) ≤ 1/100 := by
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<20000) hm
  have hmR : (20000:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hKR : (36:ℝ)≤K := by exact_mod_cast hK
  have hK0 : (0:ℝ)<K := by linarith only [hKR]
  have hKmR : 8*(K:ℝ)≤m := by exact_mod_cast hKm
  let f : Finset (Fin m) → ℝ := fun Γ => (selectedGapAdjacencies Γ).card
  have hvariance : rankAverage K (fun Γ => (f Γ-(K:ℝ)^2/(m:ℝ))^2) ≤
      2*(K:ℝ)^2/(m:ℝ) := by
    rw [rankAverage_centered_square]
    change rankAverage K (fun Γ => ((selectedGapAdjacencies Γ).card:ℝ)^2) -
      2*((K:ℝ)^2/(m:ℝ))*rankAverage K (fun Γ => ((selectedGapAdjacencies Γ).card:ℝ))+
      ((K:ℝ)^2/(m:ℝ))^2 ≤ _
    rw [hfirst]
    have hs : (K:ℝ)^4/(m:ℝ)^2+4*(K:ℝ)^3/(m:ℝ)^2+(K:ℝ)^2/(m:ℝ)-
        2*((K:ℝ)^2/(m:ℝ))*((K:ℝ)*((K:ℝ)-1)/(m:ℝ))+
        ((K:ℝ)^2/(m:ℝ))^2 =
        6*(K:ℝ)^3/(m:ℝ)^2+(K:ℝ)^2/(m:ℝ) := by
      field_simp [hm0.ne']
      <;> ring
    have htop : 6*(K:ℝ)^3/(m:ℝ)^2+(K:ℝ)^2/(m:ℝ) ≤
        2*(K:ℝ)^2/(m:ℝ) := by
      have hk : 6*(K:ℝ)≤m := by linarith only [hKmR,hK0]
      have hmul := mul_le_mul_of_nonneg_right hk (sq_nonneg (K:ℝ))
      have hnum : 6*(K:ℝ)^3≤(K:ℝ)^2*(m:ℝ) := by nlinarith only [hmul]
      have hf : 6*(K:ℝ)^3/(m:ℝ)^2≤(K:ℝ)^2/(m:ℝ) := by
        calc
          _≤((K:ℝ)^2*(m:ℝ))/(m:ℝ)^2 := div_le_div_of_le (sq_nonneg _) hnum
          _=_ := by field_simp [hm0.ne']; ring
      calc
        _ ≤ (K:ℝ)^2/(m:ℝ)+(K:ℝ)^2/(m:ℝ) := add_le_add_right hf _
        _ = _ := by ring
    linarith only [hsecond, hs, htop]
  have hmark := event_fraction_mul_square_le (K:=K) (badIsolatedEvent m K) f
    ((K:ℝ)^2/(m:ℝ)) ((K:ℝ)/9) (by positivity)
    (fun ρ hρ => bad_event_gap hmpos hK hKm ρ hρ)
  have hb : (((badIsolatedEvent m K).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)))*
      ((K:ℝ)/9)^2 ≤ 2*(K:ℝ)^2/(m:ℝ) := hmark.trans hvariance
  have hgap : (0:ℝ)<((K:ℝ)/9)^2 := by positivity
  apply (mul_le_mul_right hgap).mp
  apply hb.trans
  have he : 2*(K:ℝ)^2/(m:ℝ) ≤ (1/100:ℝ)*((K:ℝ)/9)^2 := by
    apply (div_le_iff hm0).mpr
    have hh := mul_le_mul_of_nonneg_right hmR (sq_nonneg (K:ℝ))
    nlinarith only [hh, sq_nonneg (K:ℝ)]
  exact he

#print axioms bad_fraction_le_of_moments
end MaxCaterpillar.OvernightConstants.CherryConcentration
