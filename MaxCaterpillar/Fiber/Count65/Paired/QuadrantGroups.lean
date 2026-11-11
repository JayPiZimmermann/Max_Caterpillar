import MaxCaterpillar.Fiber.Connected64.Crossing
import MaxCaterpillar.Fiber.Connected64.OutputMoves

/-! # Finite knot groups in homogeneous quadrant representations

Every positive-knot group has zero total jump. Its complete contribution,
including zero rows and arbitrary signed output coefficients, is one linear
form, equivalently a signed pair. These identities hold for arbitrary finite
width; they do not by themselves assert connectivity of all completions.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups

open BigOperators

variable {ι : Type*} [Fintype ι]

/-- All slots vanishing on the ray `Q = τ N`. Zero rows are harmless members. -/
noncomputable def knotGroup (a b : ι → ℝ) (τ : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => a i * τ + b i = 0)

/-- The coefficient carried by the positive orientation of a knot group. -/
noncomputable def groupCoefficient (a b d : ι → ℝ) (τ : ℝ) : ℝ :=
  ∑ i in knotGroup a b τ, d i * max 0 (a i)

theorem positive_part_product (a u : ℝ) :
    max 0 (a*u) = max 0 a * max 0 u + max 0 (-a) * max 0 (-u) := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 u with hu | hu
  · rw [max_eq_right ha, max_eq_right hu,
      max_eq_left (neg_nonpos.mpr ha), max_eq_left (neg_nonpos.mpr hu),
      max_eq_right (mul_nonneg ha hu)]
    ring
  · rw [max_eq_right ha, max_eq_left hu,
      max_eq_left (neg_nonpos.mpr ha), max_eq_right (neg_nonneg.mpr hu),
      max_eq_left (mul_nonpos_of_nonneg_of_nonpos ha hu)]
    ring
  · rw [max_eq_left ha, max_eq_right hu,
      max_eq_right (neg_nonneg.mpr ha), max_eq_left (neg_nonpos.mpr hu),
      max_eq_left (mul_nonpos_of_nonpos_of_nonneg ha hu)]
    ring
  · rw [max_eq_left ha, max_eq_left hu,
      max_eq_right (neg_nonneg.mpr ha), max_eq_right (neg_nonneg.mpr hu),
      max_eq_right (mul_nonneg_of_nonpos_of_nonpos ha hu)]
    ring

/-- An arbitrary finite collection on one ray whose jumps cancel is globally
linear, including outside the quadrant. -/
theorem finite_aligned_group_linear (s : Finset ι) (a b d : ι → ℝ) (τ : ℝ)
    (haligned : ∀ i ∈ s, a i * τ + b i = 0)
    (hjump : (∑ i in s, d i * |a i|) = 0) (Q N : ℝ) :
    (∑ i in s, d i * max 0 (a i*Q+b i*N)) =
      (∑ i in s, d i * max 0 (a i)) * (Q-τ*N) := by
  let P := ∑ i in s, d i * max 0 (a i)
  let M := ∑ i in s, d i * max 0 (-a i)
  have hPM : P+M = 0 := by
    dsimp [P,M]
    rw [← Finset.sum_add_distrib]
    convert hjump using 1
    apply Finset.sum_congr rfl
    intro i _hi
    have h := max_zero_add_max_neg_zero_eq_abs_self (a i)
    rw [max_comm (a i) 0, max_comm (-a i) 0] at h
    rw [← h]
    ring
  have heval : (∑ i in s, d i * max 0 (a i*Q+b i*N)) =
      P * max 0 (Q-τ*N)+M * max 0 (-(Q-τ*N)) := by
    dsimp [P,M]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hb : b i = -(a i*τ) := by linarith only [haligned i hi]
    have hf : a i*Q+b i*N = a i*(Q-τ*N) := by rw [hb]; ring
    rw [hf,positive_part_product]
    ring
  have hdiff : max 0 (Q-τ*N)-max 0 (-(Q-τ*N)) = Q-τ*N := by
    simpa only [max_comm] using max_zero_sub_max_neg_zero_eq_self (Q-τ*N)
  change _ = P * (Q-τ*N)
  rw [heval]
  have hM : M = -P := by linarith only [hPM]
  rw [hM]
  calc
    _ = P * (max 0 (Q-τ*N)-max 0 (-(Q-τ*N))) := by ring
    _ = P * (Q-τ*N) := by rw [hdiff]

theorem knotGroup_jump_zero (a b d : ι → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i * max 0 (a i*Q+b i*N)) = Q-N) :
    (∑ i in knotGroup a b τ, d i * |a i|) = 0 := by
  apply Connected64.interior_knot_jump_zero a b d 1 (-1) τ hτ
  intro x hx
  simpa only [mul_one, one_mul, sub_eq_add_neg] using hfit x 1 hx (by norm_num)

/-- Every positive knot group of any finite exact quadrant representation is
one linear contribution. There is no upper bound on the number of slots. -/
theorem knotGroup_linear (a b d : ι → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i * max 0 (a i*Q+b i*N)) = Q-N) (Q N : ℝ) :
    (∑ i in knotGroup a b τ, d i * max 0 (a i*Q+b i*N)) =
      groupCoefficient a b d τ * (Q-τ*N) := by
  apply finite_aligned_group_linear
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · exact knotGroup_jump_zero a b d τ hτ hfit

/-- The same group may be replaced algebraically by a signed pair, even when
its coefficient is zero or negative. -/
theorem knotGroup_signedPair (a b d : ι → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i * max 0 (a i*Q+b i*N)) = Q-N) (Q N : ℝ) :
    (∑ i in knotGroup a b τ, d i * max 0 (a i*Q+b i*N)) =
      groupCoefficient a b d τ * max 0 (Q-τ*N) -
      groupCoefficient a b d τ * max 0 (-(Q-τ*N)) := by
  rw [knotGroup_linear a b d τ hτ hfit Q N, ← mul_sub]
  congr 1
  symm
  simpa only [max_comm] using max_zero_sub_max_neg_zero_eq_self (Q-τ*N)

theorem knotGroup_orientation_balance (a b d : ι → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i * max 0 (a i*Q+b i*N)) = Q-N) :
    (∑ i in knotGroup a b τ, d i * max 0 (-a i)) =
      -groupCoefficient a b d τ := by
  have hjump := knotGroup_jump_zero a b d τ hτ hfit
  have hsplit : (∑ i in knotGroup a b τ, d i * |a i|) =
      groupCoefficient a b d τ+
        (∑ i in knotGroup a b τ, d i * max 0 (-a i)) := by
    unfold groupCoefficient
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    have h := max_zero_add_max_neg_zero_eq_abs_self (a i)
    rw [max_comm (a i) 0,max_comm (-a i) 0] at h
    rw [← h]
    ring
  rw [hsplit] at hjump
  linarith only [hjump]

/-- A group carrying a nonzero linear form has actual effective slots of
both orientations. Thus its signed pair can use existing physical slots. -/
theorem knotGroup_nonzero_has_opposite_slots (a b d : ι → ℝ) (τ : ℝ)
    (hτ : 0 < τ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i * max 0 (a i*Q+b i*N)) = Q-N)
    (hP : groupCoefficient a b d τ ≠ 0) :
    ∃ p n : ι, p ∈ knotGroup a b τ ∧ n ∈ knotGroup a b τ ∧
      d p ≠ 0 ∧ d n ≠ 0 ∧ 0 < a p ∧ a n < 0 ∧ p ≠ n := by
  rcases Finset.exists_ne_zero_of_sum_ne_zero hP with ⟨p,hp,hdp⟩
  have hM : (∑ i in knotGroup a b τ, d i * max 0 (-a i)) ≠ 0 := by
    rw [knotGroup_orientation_balance a b d τ hτ hfit]
    exact neg_ne_zero.mpr hP
  rcases Finset.exists_ne_zero_of_sum_ne_zero hM with ⟨n,hn,hdn⟩
  have hap : 0 < a p := by
    by_contra h
    exact hdp (by rw [max_eq_left (le_of_not_gt h),mul_zero])
  have han : a n < 0 := by
    by_contra h
    exact hdn (by rw [max_eq_left (neg_nonpos.mpr (le_of_not_gt h)),mul_zero])
  refine ⟨p,n,hp,hn,?_,?_,hap,han,?_⟩
  · exact (mul_ne_zero_iff.mp hdp).1
  · exact (mul_ne_zero_iff.mp hdn).1
  · intro hpn
    rw [hpn] at hap
    linarith only [hap,han]

/-- A zero-coefficient knot group cancels globally, with no positivity
restriction on the inputs to its common linear form. -/
theorem knotGroup_zero_cancels (a b d : ι → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i * max 0 (a i*Q+b i*N)) = Q-N)
    (hP : groupCoefficient a b d τ = 0) (Q N : ℝ) :
    (∑ i in knotGroup a b τ, d i * max 0 (a i*Q+b i*N)) = 0 := by
  rw [knotGroup_linear a b d τ hτ hfit Q N,hP,zero_mul]

/-- Exhaustive single-slot classification, including quadrant boundaries. -/
theorem gate_classification (a b : ℝ) :
    (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) ∨
      ∃ τ : ℝ, 0 < τ ∧ a ≠ 0 ∧ a*τ+b = 0 := by
  by_cases hc : a*b < 0
  · exact Or.inr (Or.inr ((Connected64.crossing_iff_positive_knot a b).mp hc))
  rcases Connected64.coefficients_same_sign_of_no_interior_knot a b
    (fun τ hτ ha hz => hc
      ((Connected64.crossing_iff_positive_knot a b).mpr ⟨τ,hτ,ha,hz⟩)) with hp | hn
  · exact Or.inl hp
  · exact Or.inr (Or.inl hn)

/-- If no effective crossing remains, all surviving slots are nonnegative
linear forms or identically dormant on the quadrant. -/
theorem no_crossing_normal_form (a b d : ι → ℝ)
    (hno : ∀ i, d i ≠ 0 → ¬ a i*b i < 0) :
    ∀ i, d i = 0 ∨ (0 ≤ a i ∧ 0 ≤ b i) ∨ (a i ≤ 0 ∧ b i ≤ 0) := by
  intro i
  by_cases hd : d i = 0
  · exact Or.inl hd
  rcases gate_classification (a i) (b i) with hp | hn | ⟨τ,hτ,ha,hz⟩
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr hn)
  · exact False.elim (hno i hd
      ((Connected64.crossing_iff_positive_knot _ _).mpr ⟨τ,hτ,ha,hz⟩))

/-- Exact coefficient totals obtained from the two quadrant axes. -/
theorem quadrant_axis_weights (a b d : ι → ℝ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i * max 0 (a i*Q+b i*N)) = Q-N) :
    (∑ i, d i * max 0 (a i)) = 1 ∧
      (∑ i, d i * max 0 (b i)) = -1 := by
  constructor
  · simpa using hfit 1 0 (by norm_num) (by norm_num)
  · simpa using hfit 0 1 (by norm_num) (by norm_num)

/-- A change to only two readout entries. All other physical coefficients are
left untouched, without requiring a consecutive arrangement of slots. -/
noncomputable def proportionalTransferOutput {k : ℕ} (d : Fin k → ℝ)
    (i j : Fin k) (c : ℝ) : Fin k → ℝ :=
  fun l => d l + (if l=j then c*d i else 0) - (if l=i then d i else 0)

theorem proportionalTransfer_source {k : ℕ} (d : Fin k → ℝ)
    (i j : Fin k) (c : ℝ) (hij : i ≠ j) :
    proportionalTransferOutput d i j c i = 0 := by
  simp [proportionalTransferOutput,hij]

theorem proportionalTransfer_spectator {k : ℕ} (d : Fin k → ℝ)
    (i j l : Fin k) (c : ℝ) (hli : l ≠ i) (hlj : l ≠ j) :
    proportionalTransferOutput d i j c l = d l := by
  simp [proportionalTransferOutput,hli,hlj]

theorem proportionalTransfer_eval {N m k : ℕ} (net : Network N m k)
    (i j : Fin k) (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ l, net.W₂ i l = c*net.W₂ j l)
    (hbias : net.b₂ i = c*net.b₂ j) (x : Point N) :
    (withOutput net (proportionalTransferOutput net.w₃ i j c) net.b₃).eval x =
      net.eval x := by
  have hpre : (∑ l, net.W₂ i l * relu ((∑ z, net.W₁ l z*x z)+net.b₁ l))+
      net.b₂ i = c*((∑ l, net.W₂ j l *
        relu ((∑ z, net.W₁ l z*x z)+net.b₁ l))+net.b₂ j) := by
    simp_rw [hrow,hbias,mul_assoc]
    rw [← Finset.mul_sum]
    ring
  have hact : relu ((∑ l, net.W₂ i l * relu ((∑ z, net.W₁ l z*x z)+net.b₁ l))+
      net.b₂ i) = c*relu ((∑ l, net.W₂ j l *
        relu ((∑ z, net.W₁ l z*x z)+net.b₁ l))+net.b₂ j) := by
    rw [hpre]
    change max 0 (c*_) = c*max 0 _
    rw [mul_max_of_nonneg _ _ hc,mul_zero]
  unfold withOutput Network.eval proportionalTransferOutput
  simp only [add_mul,sub_mul,ite_mul,zero_mul,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [hact]
  ring

/-- Same-orientation proportional gates merge by an actual continuous output
path. The first matrix, second matrix, every bias, and all spectator outputs
remain fixed. This handles signed and zero output weights. -/
noncomputable def proportionalTransferPath {N m k : ℕ} [NeZero N]
    (net : ExactFiber N m k) (i j : Fin k) (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ l, net.val.W₂ i l = c*net.val.W₂ j l)
    (hbias : net.val.b₂ i = c*net.val.b₂ j) :
    Path net (⟨withOutput net.val
      (proportionalTransferOutput net.val.w₃ i j c) net.val.b₃,
      fun x => (proportionalTransfer_eval net.val i j c hc hrow hbias x).trans
        (net.property x)⟩ : ExactFiber N m k) :=
  outputInterpolationPath net (proportionalTransferOutput net.val.w₃ i j c)
    net.val.b₃ (fun x =>
      (proportionalTransfer_eval net.val i j c hc hrow hbias x).trans (net.property x))

end MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups
