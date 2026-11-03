import MaxCaterpillar.Frontier.Basic

/-! A necessary zero of an outer preactivation at every three-way top tie.
The raw shallow functions below permit arbitrary biases and signed coefficients.
No support restriction, root-direction assumption, or sign assumption is used. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.TripleContact
open BigOperators Filter Topology Frontier

variable {N : ℕ}

/-- A continuous locally odd-linear function stays locally odd-linear after
ReLU at a point where its value is nonzero. -/
theorem relu_locOddLin_of_ne_zero {f : Point N → ℝ} {q : Point N}
    (hf : LocOddLin f q) (hc : Continuous f) (hne : f q ≠ 0) :
    LocOddLin (fun x => relu (f x)) q := by
  obtain ⟨c, hodd⟩ := hf
  have hplus (v : Point N) :
      Tendsto (fun ε : ℝ => f (q + ε • v)) (𝓝[>] 0) (𝓝 (f q)) := by
    have h : Continuous (fun ε : ℝ => f (q + ε • v)) :=
      hc.comp (continuous_const.add (continuous_id.smul continuous_const))
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hminus (v : Point N) :
      Tendsto (fun ε : ℝ => f (q - ε • v)) (𝓝[>] 0) (𝓝 (f q)) := by
    have h : Continuous (fun ε : ℝ => f (q - ε • v)) :=
      hc.comp (continuous_const.sub (continuous_id.smul continuous_const))
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  rcases lt_or_gt_of_ne hne with hn | hp
  · refine ⟨0, fun v => ?_⟩
    filter_upwards [(hplus v).eventually (gt_mem_nhds hn),
      (hminus v).eventually (gt_mem_nhds hn)] with ε h1 h2
    rw [relu_of_nonpos h1.le, relu_of_nonpos h2.le, lin_zero_left]
    ring
  · refine ⟨c, fun v => ?_⟩
    filter_upwards [hodd v, (hplus v).eventually (lt_mem_nhds hp),
      (hminus v).eventually (lt_mem_nhds hp)] with ε h h1 h2
    rw [relu_of_nonneg h1.le, relu_of_nonneg h2.le]
    exact h

/-- Rescaling the input transports local odd linearity. -/
theorem locOddLin_comp_smul {f : Point N → ℝ} (q : Point N) (s : ℝ)
    (hf : LocOddLin f (s • q)) : LocOddLin (fun x => f (s • x)) q := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨s • c, fun v => ?_⟩
  filter_upwards [hc (s • v)] with ε h
  have hp : s • (q + ε • v) = s • q + ε • (s • v) := by
    rw [smul_add, smul_comm s ε v]
  have hm : s • (q - ε • v) = s • q - ε • (s • v) := by
    rw [smul_sub, smul_comm s ε v]
  rw [hp, hm, h, lin_smul_right, lin_smul_left]

/-- The three-way-tie obstruction only needs a positive gap below the top. -/
theorem not_locOddLin_max_of_gap [NeZero N] (q : Point N)
    (I : Finset (Fin N)) (hI : 3 ≤ I.card) (δ : ℝ) (hδ : 0 < δ)
    (hq0 : ∀ i ∈ I, q i = 0) (hq1 : ∀ i ∉ I, q i ≤ -δ) :
    ¬ LocOddLin (Maximum N) q := by
  intro hf
  let q' : Point N := δ⁻¹ • q
  have hscale : δ • q' = q := by simp [q', smul_smul, hδ.ne']
  have ht : LocOddLin (fun x => Maximum N (δ • x)) q' :=
    locOddLin_comp_smul q' δ (hscale.symm ▸ hf)
  have hm : LocOddLin (Maximum N) q' := (ht.const_mul δ⁻¹).congr fun x => by
    rw [Maximum_smul hδ]
    field_simp
    ring
  apply not_locOddLin_max q' I hI (fun i hi => by simp [q', hq0 i hi]) ?_ hm
  intro i hi
  change δ⁻¹ * q i ≤ -1
  have h := mul_le_mul_of_nonneg_left (hq1 i hi) (inv_nonneg.mpr hδ.le)
  have he : δ⁻¹ * (-δ) = -1 := by field_simp
  exact he ▸ h

/-- This is a literal affine-plus-one-hidden-layer expression. -/
noncomputable def shallow {m : ℕ} (a : Point N) (b : ℝ) (A : Fin m → Point N)
    (β c : Fin m → ℝ) (x : Point N) : ℝ :=
  lin a x + b + ∑ j, c j * relu (lin (A j) x + β j)

theorem continuous_lin (a : Point N) : Continuous (lin a) := by
  unfold lin
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)

theorem shallow_continuous {m : ℕ} (a : Point N) (b : ℝ)
    (A : Fin m → Point N) (β c : Fin m → ℝ) : Continuous (shallow a b A β c) := by
  apply Continuous.add ((continuous_lin a).add continuous_const)
  exact continuous_finset_sum _ fun j _ => continuous_const.mul
    (continuous_relu.comp ((continuous_lin (A j)).add continuous_const))

theorem shallow_locOddLin {m : ℕ} (a : Point N) (b : ℝ)
    (A : Fin m → Point N) (β c : Fin m → ℝ) (q : Point N) :
    LocOddLin (shallow a b A β c) q := by
  apply LocOddLin.add (((locAff_lin a q).add (locAff_const b q)).locOddLin)
  exact LocOddLin.sum _ fun j _ =>
    (((locAff_lin (A j) q).add (locAff_const (β j) q)).relu_locOddLin).const_mul (c j)

/-- With any finite number of signed outer folds, a three-way top tie must
lie on at least one core's zero set. -/
theorem exists_zero_core_at_top_tie [NeZero N] {k : ℕ}
    (R : Point N → ℝ) (g : Fin k → Point N → ℝ) (d : Fin k → ℝ)
    (q : Point N) (I : Finset (Fin N)) (hI : 3 ≤ I.card)
    (hq0 : ∀ i ∈ I, q i = 0) (hq1 : ∀ i ∉ I, q i ≤ -1)
    (hR : LocOddLin R q) (hg : ∀ j, LocOddLin (g j) q)
    (hc : ∀ j, Continuous (g j))
    (heq : ∀ x, R x + ∑ j, d j * relu (g j x) = Maximum N x) :
    ∃ j, g j q = 0 := by
  by_contra h
  have hn : ∀ j, g j q ≠ 0 := by simpa using h
  have hfold : LocOddLin (fun x => ∑ j, d j * relu (g j x)) q :=
    LocOddLin.sum _ fun j _ =>
      (relu_locOddLin_of_ne_zero (hg j) (hc j) (hn j)).const_mul (d j)
  exact not_locOddLin_max q I hI hq0 hq1 ((hR.add hfold).congr heq)

/-- Two outer folds: the disjunction retains all zero and strict-sign cases. -/
theorem two_cores_zero_at_top_tie [NeZero N]
    (R g h : Point N → ℝ) (q : Point N) (I : Finset (Fin N)) (hI : 3 ≤ I.card)
    (hq0 : ∀ i ∈ I, q i = 0) (hq1 : ∀ i ∉ I, q i ≤ -1)
    (hR : LocOddLin R q) (hg : LocOddLin g q) (hh : LocOddLin h q)
    (hgc : Continuous g) (hhc : Continuous h)
    (heq : ∀ x, R x + relu (g x) + relu (h x) = Maximum N x) :
    g q = 0 ∨ h q = 0 := by
  by_contra hn
  have hgn : g q ≠ 0 := fun h => hn (Or.inl h)
  have hhn : h q ≠ 0 := fun h => hn (Or.inr h)
  have ht := (hR.add (relu_locOddLin_of_ne_zero hg hgc hgn)).add
    (relu_locOddLin_of_ne_zero hh hhc hhn)
  exact not_locOddLin_max q I hI hq0 hq1 (ht.congr heq)

/-- Every point on each open three-way top face needs a zero core. In
particular, take a=t and b=1-t for the full open contact segment. -/
theorem max5_weighted_pair_contact {mR mg mh : ℕ}
    (aR ag ah : Point 5) (bR bg bh : ℝ)
    (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (Ag : Fin mg → Point 5) (βg cg : Fin mg → ℝ)
    (Ah : Fin mh → Point 5) (βh ch : Fin mh → ℝ)
    (heq : ∀ x, shallow aR bR AR βR cR x +
      relu (shallow ag bg Ag βg cg x) + relu (shallow ah bh Ah βh ch x) = Maximum 5 x)
    (i j : Fin 5) (hij : i ≠ j) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    shallow ag bg Ag βg cg (-(a • unitVec i) - b • unitVec j) = 0 ∨
      shallow ah bh Ah βh ch (-(a • unitVec i) - b • unitVec j) = 0 := by
  let q : Point 5 := -(a • unitVec i) - b • unitVec j
  let I : Finset (Fin 5) := (Finset.univ.erase i).erase j
  have hI : 3 ≤ I.card := by
    have hj : j ∈ Finset.univ.erase i := by simp [Ne.symm hij]
    simp [I, Finset.card_erase_of_mem hj]
  by_contra hn
  have hgn : shallow ag bg Ag βg cg q ≠ 0 := fun h => hn (Or.inl h)
  have hhn : shallow ah bh Ah βh ch q ≠ 0 := fun h => hn (Or.inr h)
  have ht := ((shallow_locOddLin aR bR AR βR cR q).add
    (relu_locOddLin_of_ne_zero (shallow_locOddLin ag bg Ag βg cg q)
      (shallow_continuous ag bg Ag βg cg) hgn)).add
    (relu_locOddLin_of_ne_zero (shallow_locOddLin ah bh Ah βh ch q)
      (shallow_continuous ah bh Ah βh ch) hhn)
  apply not_locOddLin_max_of_gap q I hI (min a b) (lt_min ha hb)
    (fun k hk => ?_) (fun k hk => ?_) (ht.congr heq)
  · have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    simp [q, unitVec, hki, hkj]
  · have hki : k = i ∨ k = j := by
      by_cases hki : k = i
      · exact Or.inl hki
      · right
        by_contra hkj
        exact hk (by simp [I, hki, hkj])
    rcases hki with rfl | rfl
    · simp [q, unitVec, hij, Ne.symm hij]
    · simp [q, unitVec, hij, Ne.symm hij]

/-- In five variables this applies at each of the ten points -e_i-e_j. -/
theorem max5_pair_contact {mR mg mh : ℕ}
    (aR ag ah : Point 5) (bR bg bh : ℝ)
    (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (Ag : Fin mg → Point 5) (βg cg : Fin mg → ℝ)
    (Ah : Fin mh → Point 5) (βh ch : Fin mh → ℝ)
    (heq : ∀ x, shallow aR bR AR βR cR x +
      relu (shallow ag bg Ag βg cg x) + relu (shallow ah bh Ah βh ch x) = Maximum 5 x)
    (i j : Fin 5) (hij : i ≠ j) :
    shallow ag bg Ag βg cg (-unitVec i - unitVec j) = 0 ∨
      shallow ah bh Ah βh ch (-unitVec i - unitVec j) = 0 := by
  simpa using max5_weighted_pair_contact aR ag ah bR bg bh AR βR cR Ag βg cg Ah βh ch
    heq i j hij 1 1 (by norm_num) (by norm_num)

#check @max5_weighted_pair_contact
#print axioms max5_weighted_pair_contact
#check @max5_pair_contact
#print axioms max5_pair_contact
#check @exists_zero_core_at_top_tie
#print axioms exists_zero_core_at_top_tie
end MaxCaterpillar.Max5Optimal.TripleContact
