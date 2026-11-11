import MaxCaterpillar.Frontier.RandomRestriction.NewCountingTradeoff

/-! A tenfold sharper scalar transfer, using the existing actual counting input. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.FeedingSharp

theorem counting_raw (m A W : ℝ) (hm : 400≤m) (hA : 1≤A) (hW : 11≤W)
    (hcount : NewCountingTradeoff.CountingPrerequisite 400 m A W) :
    min (m^2/10000) (m^4/(16*A))≤975*W := by
  let Q := min (m^2/10000) (m^4/(16*A))
  have hm0 : 0≤m := by linarith only [hm]
  have hQ : 0≤Q := le_min (by positivity) (by positivity)
  let x := Real.sqrt Q
  have hx0 : 0≤x := Real.sqrt_nonneg _
  have hxsq : x^2=Q := Real.sq_sqrt hQ
  by_cases hx : 100≤x
  · let K := ⌊x⌋₊
    have hK100 : 100≤K := Nat.le_floor hx
    have hK4 : 4≤K := (by decide : 4≤100).trans hK100
    have hK0 : (0:ℝ)≤(K:ℝ) := Nat.cast_nonneg _
    have hKu : (K:ℝ)≤x := Nat.floor_le hx0
    have hKl : 99*x≤100*(K:ℝ) := by
      have hf := Nat.lt_floor_add_one x
      change x<(K:ℝ)+1 at hf
      linarith only [hf,hx]
    have hKsq : (K:ℝ)^2≤Q := by
      nlinarith only [mul_self_le_mul_self hK0 hKu,hxsq]
    have hcut : (K:ℝ)≤m/100 := by
      have h1 : Q≤m^2/10000 := min_le_left _ _
      nlinarith only [hKsq,h1,hm0,hK0]
    have hbudget : 16*A*(K:ℝ)^2≤m^4 := by
      have h2 : Q≤m^4/(16*A) := min_le_right _ _
      have hh := (le_div_iff (by positivity : 0<16*A)).mp (hKsq.trans h2)
      nlinarith only [hh]
    have hc := hcount K hK4 hcut hbudget
    have hlow : 9801*Q≤10000*(K:ℝ)^2 := by
      have hh := mul_self_le_mul_self (by positivity : 0≤99*x) hKl
      nlinarith only [hh,hxsq]
    change Q≤975*W
    nlinarith only [hlow,hc,sq_nonneg (K:ℝ)]
  · have hx100 : x<100 := lt_of_not_ge hx
    have hQ10000 : Q<10000 := by nlinarith only [hx100,hx0,hxsq]
    change Q≤975*W
    linarith only [hQ10000,hW]

theorem compare_cutoff (N n h A : ℝ) (hN : 0≤N) (hn : 520≤n)
    (hhalf : N≤2*n+1) (hA : 1≤A) (hmoment : 4*A≤81*h) :
    min (N^2) (N^4/h)≤41000*min ((n-5)^2/10000) ((n-5)^4/(16*A)) := by
  let m := n-5
  have hm0 : 0≤m := by dsimp [m]; linarith only [hn]
  have hhp : 0<h := by linarith only [hA,hmoment]
  have hscale : 45*N≤91*m := by dsimp [m]; linarith only [hhalf,hn]
  have hsquare : N^2≤(41/10:ℝ)*m^2 := by
    have hh := mul_self_le_mul_self (by positivity : 0≤45*N) hscale
    dsimp [m] at hh ⊢
    nlinarith only [hh,sq_nonneg (n-5)]
  have hthree : N≤3*m := by dsimp [m]; linarith only [hhalf,hn]
  have hsquare3 : N^2≤9*m^2 := by
    have hh := mul_self_le_mul_self hN hthree
    nlinarith only [hh]
  have hfour : N^4≤81*m^4 := by
    have hh := mul_self_le_mul_self (sq_nonneg N) hsquare3
    nlinarith only [hh]
  change _≤41000*min (m^2/10000) (m^4/(16*A))
  by_cases hc : m^2/10000≤m^4/(16*A)
  · rw [min_eq_left hc]
    exact (min_le_left _ _).trans (by linarith only [hsquare])
  · rw [min_eq_right (le_of_not_ge hc)]
    apply (min_le_right _ _).trans
    apply (div_le_iff hhp).mpr
    apply (mul_le_mul_right (by positivity : 0<16*A)).mp
    have hid : (41000*(m^4/(16*A))*h)*(16*A)=41000*m^4*h := by
      field_simp
    rw [hid]
    have h1 := mul_le_mul_of_nonneg_right hmoment (pow_nonneg hN 4)
    have h2 := mul_le_mul_of_nonneg_right hfour (le_of_lt hhp)
    have h3 := mul_nonneg (pow_nonneg hm0 4) (le_of_lt hhp)
    nlinarith only [h1,h2,h3]

theorem forty_million_tradeoff (N n h A W : ℝ) (hN : 1040≤N) (hn : 520≤n)
    (hhalf : N≤2*n+1) (hA : 1≤A) (hmoment : 4*A≤81*h)
    (hlinear : N≤2*W+2)
    (hcount : NewCountingTradeoff.CountingPrerequisite 400 (n-5) A W) :
    (1/40000000:ℝ)*min (N^2) (N^4/h)≤W := by
  have hW : 11≤W := by linarith only [hN,hlinear]
  have hraw := counting_raw (n-5) A W (by linarith only [hn]) hA hW hcount
  have hcomp := compare_cutoff N n h A (by linarith only [hN]) hn hhalf hA hmoment
  linarith only [hraw,hcomp,hW]

theorem linear_absorption (N h W : ℝ) (hN : 1040≤N)
    (hwidth : N^3<1000*h) (hlinear : N≤2*W+2) :
    (1/40000000:ℝ)*min (N^2) (N^4/h)≤W := by
  have hNp : 0<N := by linarith only [hN]
  have hhp : 0<h := by nlinarith only [hwidth,pow_pos hNp 3]
  have hratio : N^4/h≤1000*N := by
    apply (div_le_iff hhp).mpr
    have hh := mul_le_mul_of_nonneg_left hwidth.le hNp.le
    nlinarith only [hh]
  have hmin := (min_le_right (N^2) (N^4/h)).trans hratio
  linarith only [hmin,hlinear,hN]

#print axioms counting_raw
#print axioms compare_cutoff
#print axioms forty_million_tradeoff
#print axioms linear_absorption
end MaxCaterpillar.Frontier.RandomRestriction.FeedingSharp
