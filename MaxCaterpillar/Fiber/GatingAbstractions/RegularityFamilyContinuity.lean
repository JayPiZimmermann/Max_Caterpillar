import MaxCaterpillar.Fiber.GatingAbstractions.RegularityFamily
import MaxCaterpillar.Fiber.GatingAbstractions.RegularityTopology

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.GatingAbstractions.RegularityFamily
open BigOperators Frontier Filter Topology

/-- Every denominator actually used in the rational reconstruction is nonzero. -/
def Denominators (p : Params) : Prop :=
  p 0 ≠ 0 ∧ p 1 ≠ 0 ∧ p 2 ≠ 0 ∧ p 5 ≠ 0 ∧ det p ≠ 0 ∧
  lu p ≠ 0 ∧ lv p ≠ 0 ∧ p 8 ≠ 0 ∧ p 10 ≠ 0

lemma Good.denominators {p : Params} (hp : Good p) : Denominators p := by
  rcases hp with ⟨h0,h1,h2,h5,hd,hu,hv,h8,h9,h10,hH,hG⟩
  exact ⟨h0.ne',h1.ne',h2,h5,hd,hu.ne,hv.ne,h8.ne',h10.ne'⟩

private lemma cc (p : Params) (i : Fin 17) :
    ContinuousAt (fun q : Params => q i) p := (continuous_apply i).continuousAt

lemma continuousAt_det (p : Params) : ContinuousAt det p :=
  ((cc p 2).mul (cc p 5)).sub ((cc p 3).mul (cc p 4))

lemma continuousAt_lu (p : Params) (hp : p 2 ≠ 0) : ContinuousAt lu p :=
  (cc p 6).div (cc p 2) hp

lemma continuousAt_lv (p : Params) (hp : p 5 ≠ 0) : ContinuousAt lv p :=
  (cc p 7).div (cc p 5) hp

lemma continuousAt_uRead (p : Params) (h2 : p 2 ≠ 0) (hu : lu p ≠ 0)
    (j : Fin 6) : ContinuousAt (fun q => uRead q j) p := by
  fin_cases j
  · change ContinuousAt (fun _ : Params => (0 : ℝ)) p
    exact continuousAt_const
  · change ContinuousAt (fun _ : Params => (0 : ℝ)) p
    exact continuousAt_const
  · change ContinuousAt (fun _ : Params => (1 : ℝ)) p
    exact continuousAt_const
  · change ContinuousAt (fun q : Params => 1/lu q) p
    exact continuousAt_const.div (continuousAt_lu p h2) hu
  · change ContinuousAt (fun _ : Params => (0 : ℝ)) p
    exact continuousAt_const
  · change ContinuousAt (fun _ : Params => (0 : ℝ)) p
    exact continuousAt_const

lemma continuousAt_vRead (p : Params) (h5 : p 5 ≠ 0) (hv : lv p ≠ 0)
    (j : Fin 6) : ContinuousAt (fun q => vRead q j) p := by
  fin_cases j
  · change ContinuousAt (fun _ : Params => (0 : ℝ)) p
    exact continuousAt_const
  · change ContinuousAt (fun _ : Params => (0 : ℝ)) p
    exact continuousAt_const
  · change ContinuousAt (fun _ : Params => (0 : ℝ)) p
    exact continuousAt_const
  · change ContinuousAt (fun _ : Params => (0 : ℝ)) p
    exact continuousAt_const
  · change ContinuousAt (fun _ : Params => (1 : ℝ)) p
    exact continuousAt_const
  · change ContinuousAt (fun q : Params => 1/lv q) p
    exact continuousAt_const.div (continuousAt_lv p h5) hv

private lemma continuousAt_vec4 {p : Params} (f₀ f₁ f₂ f₃ : Params → ℝ)
    (h₀ : ContinuousAt f₀ p) (h₁ : ContinuousAt f₁ p)
    (h₂ : ContinuousAt f₂ p) (h₃ : ContinuousAt f₃ p) :
    ContinuousAt (fun q => ![f₀ q,f₁ q,f₂ q,f₃ q]) p := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃

lemma continuousAt_firstRows_vec (p : Params) (h2 : p 2 ≠ 0) (h5 : p 5 ≠ 0)
    (j : Fin 6) : ContinuousAt (fun q => firstRows q j) p := by
  fin_cases j
  · change ContinuousAt (fun q : Params => ![q 0,-q 0,0,0]) p
    exact continuousAt_vec4 _ _ _ _ (cc p 0) (cc p 0).neg continuousAt_const continuousAt_const
  · change ContinuousAt (fun q : Params => ![0,0,q 1,-q 1]) p
    exact continuousAt_vec4 _ _ _ _ continuousAt_const continuousAt_const (cc p 1) (cc p 1).neg
  · change ContinuousAt (fun q : Params => ![0,q 2,0,q 3]) p
    exact continuousAt_vec4 _ _ _ _ continuousAt_const (cc p 2) continuousAt_const (cc p 3)
  · change ContinuousAt (fun q : Params => ![0,lu q*q 2,0,lu q*q 3]) p
    exact continuousAt_vec4 _ _ _ _ continuousAt_const
      ((continuousAt_lu p h2).mul (cc p 2)) continuousAt_const
      ((continuousAt_lu p h2).mul (cc p 3))
  · change ContinuousAt (fun q : Params => ![0,q 4,0,q 5]) p
    exact continuousAt_vec4 _ _ _ _ continuousAt_const (cc p 4) continuousAt_const (cc p 5)
  · change ContinuousAt (fun q : Params => ![0,lv q*q 4,0,lv q*q 5]) p
    exact continuousAt_vec4 _ _ _ _ continuousAt_const
      ((continuousAt_lv p h5).mul (cc p 4)) continuousAt_const
      ((continuousAt_lv p h5).mul (cc p 5))

lemma continuousAt_firstRows (p : Params) (h2 : p 2 ≠ 0) (h5 : p 5 ≠ 0)
    (j : Fin 6) (i : Fin 4) : ContinuousAt (fun q => firstRows q j i) p :=
  (continuous_apply i).continuousAt.comp (continuousAt_firstRows_vec p h2 h5 j)

lemma continuousAt_negativeRow (p : Params) (j : Fin 6) :
    ContinuousAt (fun q => negativeRow q j) p := by
  fin_cases j
  · exact cc p 11
  · exact cc p 12
  · exact cc p 13
  · exact cc p 14
  · exact cc p 15
  · exact cc p 16

lemma continuousAt_aRead (p : Params) (hp : Denominators p) (j : Fin 6) :
    ContinuousAt (fun q => aRead q j) p := by
  rcases hp with ⟨h0,h1,h2,h5,hd,hu,hv,h8,h10⟩
  exact (((cc p 5).mul (continuousAt_uRead p h2 hu j)).sub
    ((cc p 3).mul (continuousAt_vRead p h5 hv j))).div (continuousAt_det p) hd

lemma continuousAt_bRead (p : Params) (hp : Denominators p) (j : Fin 6) :
    ContinuousAt (fun q => bRead q j) p := by
  rcases hp with ⟨h0,h1,h2,h5,hd,hu,hv,h8,h10⟩
  exact ((((cc p 4).neg).mul (continuousAt_uRead p h2 hu j)).add
    ((cc p 2).mul (continuousAt_vRead p h5 hv j))).div (continuousAt_det p) hd

lemma continuousAt_aMaxRead (p : Params) (hp : Denominators p) (j : Fin 6) :
    ContinuousAt (fun q => aMaxRead q j) p := by
  by_cases hj : j=0
  · simp only [aMaxRead, if_pos hj]
    exact (continuousAt_aRead p hp j).add (continuousAt_const.div (cc p 0) hp.1)
  · simp only [aMaxRead, if_neg hj]
    exact (continuousAt_aRead p hp j).add continuousAt_const

lemma continuousAt_bMaxRead (p : Params) (hp : Denominators p) (j : Fin 6) :
    ContinuousAt (fun q => bMaxRead q j) p := by
  by_cases hj : j=1
  · simp only [bMaxRead, if_pos hj]
    exact (continuousAt_bRead p hp j).add (continuousAt_const.div (cc p 1) hp.2.1)
  · simp only [bMaxRead, if_neg hj]
    exact (continuousAt_bRead p hp j).add continuousAt_const

lemma continuousAt_positiveRow (p : Params) (hp : Denominators p) (j : Fin 6) :
    ContinuousAt (fun q => positiveRow q j) p := by
  exact ((continuousAt_bMaxRead p hp j).sub
    ((cc p 9).mul (continuousAt_negativeRow p j))).div (cc p 8) hp.2.2.2.2.2.2.2.1

lemma continuousAt_comparisonRow (p : Params) (hp : Denominators p) (j : Fin 6) :
    ContinuousAt (fun q => comparisonRow q j) p := by
  exact ((continuousAt_aMaxRead p hp j).sub (continuousAt_bMaxRead p hp j)).div
    (cc p 10) hp.2.2.2.2.2.2.2.2

noncomputable def familyRaw (p : Params) : Raw := toRaw (family p)

/-- Continuity of all forty-five physical weights; no rows are fixed in the target. -/
theorem continuousAt_familyRaw (p : Params) (hp : Denominators p) :
    ContinuousAt familyRaw p := by
  have hfirst : ContinuousAt firstRows p :=
    continuousAt_pi.mpr fun j => continuousAt_firstRows_vec p hp.2.2.1 hp.2.2.2.1 j
  have hsecond : ContinuousAt (fun q => ![positiveRow q, negativeRow q, comparisonRow q]) p := by
    apply continuousAt_pi.mpr
    intro k
    fin_cases k
    · exact continuousAt_pi.mpr fun j => continuousAt_positiveRow p hp j
    · exact continuousAt_pi.mpr fun j => continuousAt_negativeRow p j
    · exact continuousAt_pi.mpr fun j => continuousAt_comparisonRow p hp j
  have hout : ContinuousAt (fun q : Params => ![q 8,q 9,q 10]) p := by
    apply continuousAt_pi.mpr
    intro k
    fin_cases k
    · exact cc p 8
    · exact cc p 9
    · exact cc p 10
  have hb₁ : ContinuousAt (fun _ : Params => (0 : Fin 6 → ℝ)) p := continuousAt_const
  have hb₂ : ContinuousAt (fun _ : Params => (0 : Fin 3 → ℝ)) p := continuousAt_const
  have hb₃ : ContinuousAt (fun _ : Params => (0 : ℝ)) p := continuousAt_const
  have hnet : ContinuousAt family p :=
    continuousAt_network_of_arrays family p hfirst hb₁ hsecond hb₂ hout hb₃
  change ContinuousAt (toRaw ∘ family) p
  exact continuous_toRaw.continuousAt.comp hnet

/-- The chosen seventeen coordinates are reproduced exactly. -/
theorem freeCoordinates_familyRaw (p : Params) (h2 : p 2 ≠ 0) (h5 : p 5 ≠ 0) :
    freeCoordinates (familyRaw p) = p := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change p 6 / p 2 * p 2 = p 6
    field_simp [h2]
  · change p 7 / p 5 * p 5 = p 7
    field_simp [h5]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The reconstruction domain persists in a neighborhood of every one of its points. -/
theorem Good.eventually {p : Params} (hp : Good p) : ∀ᶠ q in 𝓝 p, Good q := by
  have hden := hp.denominators
  rcases hp with ⟨h0,h1,h2,h5,hd,hu,hv,h8,h9,h10,hH,hG⟩
  have H0 := (cc p 0).eventually (Ioi_mem_nhds h0)
  have H1 := (cc p 1).eventually (Ioi_mem_nhds h1)
  have H2 := (cc p 2).eventually_ne h2
  have H5 := (cc p 5).eventually_ne h5
  have HD := (continuousAt_det p).eventually_ne hd
  have HU := (continuousAt_lu p h2).eventually (Iio_mem_nhds hu)
  have HV := (continuousAt_lv p h5).eventually (Iio_mem_nhds hv)
  have H8 := (cc p 8).eventually (Ioi_mem_nhds h8)
  have H9 := (cc p 9).eventually (Iio_mem_nhds h9)
  have H10 := (cc p 10).eventually (Ioi_mem_nhds h10)
  have HH := Filter.eventually_all.mpr fun j =>
    (continuousAt_negativeRow p j).eventually (Ioi_mem_nhds (hH j))
  have HG := Filter.eventually_all.mpr fun j =>
    (continuousAt_positiveRow p hden j).eventually (Ioi_mem_nhds (hG j))
  filter_upwards [H0,H1,H2,H5,HD,HU,HV,H8,H9,H10,HH,HG] with q h0 h1 h2 h5 hd hu hv h8 h9 h10 hh hg
  exact ⟨h0,h1,h2,h5,hd,hu,hv,h8,h9,h10,hh,hg⟩

theorem isOpen_good : IsOpen {p : Params | Good p} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  exact hp.eventually

theorem continuousOn_familyRaw : ContinuousOn familyRaw {p : Params | Good p} := by
  intro p hp
  exact (continuousAt_familyRaw p hp.denominators).continuousWithinAt

/-- At each canonical positive common-offset point, the rational reconstruction
is an exact local section of the seventeen free coordinates. -/
theorem local_exact_section (c : ℝ) (hc : 0 < c) :
    ContinuousAt familyRaw (base c) ∧
    (∀ᶠ p in 𝓝 (base c),
      (∀ x, (fromRaw (familyRaw p)).eval x = Maximum 4 x) ∧
      freeCoordinates (familyRaw p) = p) := by
  have hg := good_base c hc
  refine ⟨continuousAt_familyRaw _ hg.denominators, ?_⟩
  filter_upwards [hg.eventually] with p hp
  constructor
  · rw [familyRaw, fromRaw_toRaw (family p) (family_zeroBiases p)]
    exact family_exact p hp
  · exact freeCoordinates_familyRaw p hp.2.2.1 hp.2.2.2.1

#print axioms family_exact
#print axioms local_exact_section
end MaxCaterpillar.Fiber.GatingAbstractions.RegularityFamily
