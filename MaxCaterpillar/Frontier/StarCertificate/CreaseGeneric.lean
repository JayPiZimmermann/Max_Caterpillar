import MaxCaterpillar.Frontier.StarCertificate.CreaseLine

/-! # Generic hyperplane points and cancellation of a parallel class

Generic points are constructed inside the actual open domain by finitely
many small perturbations in the target kernel. No genericity assumption is
part of the final cancellation theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators Filter Topology

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- A nonempty open slice of a hyperplane contains a point avoiding every
member of a finite family of nonparallel hyperplanes. -/
theorem exists_generic_kernel_point (U : Set (Point n)) (hU : IsOpen U)
    (w₀ : Point n) (hw : w₀ ≠ 0) (w : ι → Point n)
    (q₀ : Point n) (hq₀U : q₀ ∈ U) (hq₀ : lin w₀ q₀ = 0)
    (s : Finset ι) (hnonparallel : ∀ i ∈ s, ¬ ∃ a : ℝ, w i = a • w₀) :
    ∃ q : Point n, q ∈ U ∧ lin w₀ q = 0 ∧ ∀ i ∈ s, lin (w i) q ≠ 0 := by
  classical
  revert hnonparallel
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨q₀, hq₀U, hq₀, fun i hi => (Finset.not_mem_empty i hi).elim⟩
  | @insert i s hi ih =>
    intro hn
    obtain ⟨q, hqU, hq₀', hq⟩ :=
      ih (fun j hj => hn j (Finset.mem_insert_of_mem hj))
    by_cases hwi : lin (w i) q = 0
    · obtain ⟨u, hu₀, hui⟩ := nonparallel_kernel_witness w₀ (w i) hw
        (hn i (Finset.mem_insert_self i s))
      obtain ⟨δ, hδ, hline⟩ := open_line_interval U hU q u hqU
      have hsmall : ∀ j, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          j ∈ s → |ε * lin (w j) u| < |lin (w j) q| := by
        intro j
        by_cases hj : j ∈ s
        · filter_upwards [eventually_small (lin (w j) u) (abs_pos.mpr (hq j hj))]
            with ε hε
          exact fun _ => hε
        · exact Filter.eventually_of_forall (fun _ hj' => (hj hj').elim)
      have hall := (Filter.eventually_all.mpr hsmall).and
        (Ioo_mem_nhdsWithin_Ioi (show (0 : ℝ) ∈ Set.Ico 0 δ from ⟨le_rfl, hδ⟩))
      obtain ⟨ε, hε, hε₀, hεδ⟩ := hall.exists
      refine ⟨q + ε • u, hline ε (by rwa [abs_of_pos hε₀]), ?_, ?_⟩
      · rw [lin_add_right, lin_smul_right, hq₀', hu₀, mul_zero, add_zero]
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · rw [lin_add_right, lin_smul_right, hwi, zero_add]
          exact mul_ne_zero hε₀.ne' hui
        · intro hz
          rw [lin_add_right, lin_smul_right] at hz
          have he : ε * lin (w j) u = -lin (w j) q := by linarith only [hz]
          have hg := hε j hjs
          rw [he, abs_neg] at hg
          exact (lt_irrefl _ hg)
    · refine ⟨q, hqU, hq₀', ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact hwi
      · exact hq j hjs

/-- If a finite signed homogeneous ReLU sum agrees with an affine function
on an open set crossed by a nonzero target hyperplane, its complete class
of parallel forms has zero signed absolute amplitude. All weights are real.
The chosen multipliers may be zero, so zero forms are handled explicitly. -/
theorem open_set_parallel_crease_cancel (U : Set (Point n)) (hU : IsOpen U)
    (w : ι → Point n) (c : ι → ℝ) (l : Point n) (β : ℝ)
    (h : ∀ x ∈ U, lin l x + β = ∑ i, c i * relu (lin (w i) x))
    (w₀ : Point n) (hw : w₀ ≠ 0) (J : Finset ι) (scale : ι → ℝ)
    (hparallel : ∀ i ∈ J, w i = scale i • w₀)
    (hnonparallel : ∀ i ∉ J, ¬ ∃ a : ℝ, w i = a • w₀)
    (hcross : ∃ q : Point n, q ∈ U ∧ lin w₀ q = 0) :
    (∑ i in J, c i * |scale i|) = 0 := by
  classical
  obtain ⟨q₀, hq₀U, hq₀⟩ := hcross
  obtain ⟨q, hqU, hq, hgen⟩ := exists_generic_kernel_point U hU w₀ hw w
    q₀ hq₀U hq₀ Jᶜ (fun i hi => hnonparallel i (Finset.mem_compl.mp hi))
  obtain ⟨v, hv⟩ := exists_unit_direction w₀ hw
  exact generic_parallel_crease_balance U hU w c l β h w₀ q v J scale
    hqU hq hv hparallel (fun i hi => hgen i (Finset.mem_compl.mpr hi))

end MaxCaterpillar.Frontier.StarCertificate
