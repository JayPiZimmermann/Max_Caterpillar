import MaxCaterpillar.Fiber.PositiveKink

/-! # Exact crease mass of a finite signed affine ReLU sum -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner
open BigOperators Filter Topology MaxCaterpillar.Frontier

lemma relu_pair_abs (x : ℝ) : relu x+relu (-x)=|x| := by
  rcases le_total 0 x with hx | hx
  · rw [relu_of_nonneg hx,relu_of_nonpos (neg_nonpos.mpr hx),abs_of_nonneg hx,add_zero]
  · rw [relu_of_nonpos hx,relu_of_nonneg (neg_nonneg.mpr hx),abs_of_nonpos hx,zero_add]

lemma eventually_midpoint_formula (a b : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      relu (a*ε+b)+relu (a*(-ε)+b)-2*relu b =
        |ε| * (if b=0 then |a| else 0) := by
  by_cases hb : b=0
  · apply Filter.eventually_of_forall
    intro ε
    rw [hb,if_pos rfl]
    simp only [add_zero,mul_neg,show relu 0=0 from max_self 0,mul_zero,sub_zero]
    rw [relu_pair_abs,abs_mul]
    ring
  · filter_upwards [eventually_small a (abs_pos.mpr hb)] with ε hε
    rw [if_neg hb,mul_zero]
    have hm := relu_midpoint_eq_zero b (a*ε) (by simpa only [mul_comm] using hε.le)
    convert hm using 1 <;> congr 2 <;> congr 1 <;> ring

noncomputable def jumpMass {ι : Type*} [Fintype ι] (a b c : ι → ℝ) : ℝ :=
  ∑ i, c i*(if b i=0 then |a i| else 0)

/-- The exact local kink balance, including all zero slopes and zero weights. -/
theorem jumpMass_eq_one {ι : Type*} [Fintype ι] (a b c : ι → ℝ)
    (l γ δ : ℝ) (hδ : 0<δ)
    (h : ∀ s : ℝ, |s|<δ →
      relu s = l*s+γ+∑ i, c i*relu (a i*s+b i)) :
    jumpMass a b c=1 := by
  classical
  have hall := (Filter.eventually_all.mpr (fun i => eventually_midpoint_formula (a i) (b i))).and
    (Ioo_mem_nhdsWithin_Ioi (show (0:ℝ) ∈ Set.Ico 0 δ from ⟨le_rfl,hδ⟩))
  obtain ⟨ε,hε,hε0,hεδ⟩ := hall.exists
  have hp := h ε (by rwa [abs_of_pos hε0])
  have hm := h (-ε) (by rwa [abs_neg,abs_of_pos hε0])
  have hz := h 0 (by simpa using hδ)
  rw [relu_of_nonneg hε0.le] at hp
  rw [relu_of_nonpos (neg_nonpos.mpr hε0.le)] at hm
  simp only [show relu 0=0 from max_self 0,mul_zero,zero_add] at hz
  have he : (∑ i, c i*(relu (a i*ε+b i)+relu (a i*(-ε)+b i)-2*relu (b i))) =
      (∑ i, c i*relu (a i*ε+b i)) + (∑ i, c i*relu (a i*(-ε)+b i)) -
        2*(∑ i, c i*relu (b i)) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmass : (∑ i, c i*(relu (a i*ε+b i)+relu (a i*(-ε)+b i)-2*relu (b i))) =
      ε*jumpMass a b c := by
    simp_rw [hε,abs_of_pos hε0]
    unfold jumpMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hεmass : ε*jumpMass a b c=ε := by
    rw [← hmass,he]
    linarith only [hp,hm,hz]
  exact (mul_left_cancel₀ hε0.ne' (by simpa only [mul_one] using hεmass))

#print axioms jumpMass_eq_one
end MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner
