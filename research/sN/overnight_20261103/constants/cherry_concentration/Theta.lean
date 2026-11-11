import research.sN.overnight_20261103.constants.cherry_concentration.Actual

/-! More isolated gaps with a constant failure bound.
All moments and event fractions concern literal finite rank permutations. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.OvernightConstants.CherryConcentration
open BigOperators Frontier.RandomRestriction.GoodEvent
variable {m K : ℕ}

/-- The existing first and second moments imply a uniform centered-square bound. -/
theorem actual_centered_moment_le (hm : 2≤m) (hKm : 5*K≤m) :
    rankAverage K (fun Γ : Finset (Fin m) =>
      (((selectedGapAdjacencies Γ).card:ℝ)-(K:ℝ)^2/(m:ℝ))^2) ≤
      2*(K:ℝ)^2/(m:ℝ) := by
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<2) hm
  have hm0 : (0:ℝ)<m := by exact_mod_cast hmpos
  have hKle : K≤m := by linarith only [hKm]
  have hKmR : 5*(K:ℝ)≤m := by exact_mod_cast hKm
  have hfirst := rankAverage_selectedGapAdjacencies_eq hm hKle
  have hsecond := Overnight.Constants.Cherry.rankAverage_adjacency_square_le hmpos hKle
  rw [rankAverage_centered_square,hfirst]
  have hs : (K:ℝ)^4/(m:ℝ)^2+3*(K:ℝ)^3/(m:ℝ)^2+(K:ℝ)^2/(m:ℝ)-
      2*((K:ℝ)^2/(m:ℝ))*((K:ℝ)*((K:ℝ)-1)/(m:ℝ))+
      ((K:ℝ)^2/(m:ℝ))^2 =
      5*(K:ℝ)^3/(m:ℝ)^2+(K:ℝ)^2/(m:ℝ) := by
    field_simp [hm0.ne']
    <;> ring
  have htop : 5*(K:ℝ)^3/(m:ℝ)^2+(K:ℝ)^2/(m:ℝ) ≤
      2*(K:ℝ)^2/(m:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hKmR (sq_nonneg (K:ℝ))
    have hnum : 5*(K:ℝ)^3≤(K:ℝ)^2*(m:ℝ) := by nlinarith only [hmul]
    have hf : 5*(K:ℝ)^3/(m:ℝ)^2≤(K:ℝ)^2/(m:ℝ) := by
      calc
        _≤((K:ℝ)^2*(m:ℝ))/(m:ℝ)^2 := div_le_div_of_le (sq_nonneg _) hnum
        _=_ := by field_simp [hm0.ne']; ring
    calc
      _ ≤ (K:ℝ)^2/(m:ℝ)+(K:ℝ)^2/(m:ℝ) := add_le_add_right hf _
      _ = _ := by ring
  linarith only [hsecond,hs,htop]

/-- Actual rank permutations with fewer than 7K/10 isolated nonanchor gaps. -/
noncomputable def highBadIsolatedEvent (m K : ℕ) : Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter fun ρ =>
    ((isolatedGaps (smallRankGaps ρ K)).card:ℝ)<(7/10:ℝ)*(K:ℝ)

@[simp] theorem mem_highBadIsolatedEvent (ρ : Equiv.Perm (Fin m)) :
    ρ∈highBadIsolatedEvent m K ↔
      ((isolatedGaps (smallRankGaps ρ K)).card:ℝ)<(7/10:ℝ)*(K:ℝ) := by
  classical
  simp only [highBadIsolatedEvent,Finset.mem_filter,Finset.mem_univ,true_and]

theorem high_bad_event_gap (hm : 0<m) (hK : 50≤K) (hKm : 10*K≤m)
    (ρ : Equiv.Perm (Fin m)) (hρ : ρ∈highBadIsolatedEvent m K) :
    (K:ℝ)^2/(m:ℝ)+(K:ℝ)/25 ≤
      ((selectedGapAdjacencies (smallRankGaps ρ K)).card:ℝ) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hKR : (50:ℝ)≤K := by exact_mod_cast hK
  have hKmR : 10*(K:ℝ)≤m := by exact_mod_cast hKm
  have hKle : K≤m := by linarith only [hKm]
  have hc := card_le_isolated_add_one_add_two_adjacent (smallRankGaps ρ K)
  rw [card_smallRankGaps hKle] at hc
  have hcR : (K:ℝ)≤((isolatedGaps (smallRankGaps ρ K)).card:ℝ)+1+
      2*((selectedGapAdjacencies (smallRankGaps ρ K)).card:ℝ) := by exact_mod_cast hc
  have hbad := (mem_highBadIsolatedEvent ρ).mp hρ
  have hcenter : (K:ℝ)^2/(m:ℝ)≤(K:ℝ)/10 := by
    apply (div_le_iff hmR).mpr
    have hh := mul_le_mul_of_nonneg_left hKmR (Nat.cast_nonneg (α:=ℝ) K)
    nlinarith only [hh]
  linarith only [hcR,hbad,hKR,hcenter]

/-- A closed quantitative bound; no moment or probability estimate is a premise. -/
theorem highBad_fraction_le (hm : 2≤m) (hK : 50≤K) (hKm : 10*K≤m) :
    ((highBadIsolatedEvent m K).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)) ≤
      1250/(m:ℝ) := by
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<2) hm
  have hm0 : (0:ℝ)<m := by exact_mod_cast hmpos
  have hK0 : (0:ℝ)<K := by exact_mod_cast lt_of_lt_of_le (by decide : 0<50) hK
  let f : Finset (Fin m)→ℝ := fun Γ => (selectedGapAdjacencies Γ).card
  have hvariance := actual_centered_moment_le hm (by linarith only [hKm] : 5*K≤m)
  have hmark := event_fraction_mul_square_le (K:=K) (highBadIsolatedEvent m K) f
    ((K:ℝ)^2/(m:ℝ)) ((K:ℝ)/25) (by positivity)
    (fun ρ hρ => high_bad_event_gap hmpos hK hKm ρ hρ)
  have hb : (((highBadIsolatedEvent m K).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)))*
      ((K:ℝ)/25)^2 ≤ 2*(K:ℝ)^2/(m:ℝ) := hmark.trans hvariance
  apply (mul_le_mul_right (by positivity : (0:ℝ)<((K:ℝ)/25)^2)).mp
  calc
    _ ≤ 2*(K:ℝ)^2/(m:ℝ) := hb
    _ = (1250/(m:ℝ))*((K:ℝ)/25)^2 := by ring

/-- At least15/16 of actual rank permutations have at least7K/10 isolated gaps. -/
theorem highBad_fraction_le_sixteenth (hm : 20000≤m) (hK : 50≤K) (hKm : 10*K≤m) :
    ((highBadIsolatedEvent m K).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)) ≤ 1/16 := by
  have hm0 : (0:ℝ)<m := by exact_mod_cast lt_of_lt_of_le (by decide : 0<20000) hm
  have hmR : (20000:ℝ)≤m := by exact_mod_cast hm
  apply (highBad_fraction_le ((by decide : 2≤20000).trans hm) hK hKm).trans
  exact (div_le_iff hm0).mpr (by linarith only [hmR])

theorem highBad_fraction_le_tenth (hm : 20000≤m) (hK : 50≤K) (hKm : 10*K≤m) :
    ((highBadIsolatedEvent m K).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)) ≤ 1/10 :=
  (highBad_fraction_le_sixteenth hm hK hKm).trans (by norm_num)

/-- The intended cutoff satisfies the hypotheses without a divisibility assumption. -/
theorem highBad_tenth_cutoff (hm : 20000≤m) :
    ((highBadIsolatedEvent m (m/10)).card:ℝ)/Fintype.card (Equiv.Perm (Fin m)) ≤ 1/16 := by
  apply highBad_fraction_le_sixteenth hm
  · exact (Nat.le_div_iff_mul_le (by decide : 0<10)).mpr
      ((by decide : 50*10≤20000).trans hm)
  · simpa only [Nat.mul_comm] using Nat.div_mul_le_self m 10

#check @actual_centered_moment_le
#check @highBad_fraction_le
#check @highBad_fraction_le_tenth
#print axioms actual_centered_moment_le
#print axioms highBad_fraction_le
#print axioms highBad_fraction_le_sixteenth
#print axioms highBad_fraction_le_tenth
#print axioms highBad_tenth_cutoff
end MaxCaterpillar.OvernightConstants.CherryConcentration
