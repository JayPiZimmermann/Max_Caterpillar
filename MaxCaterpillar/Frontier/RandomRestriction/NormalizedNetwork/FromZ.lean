import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model

/-! # Exact all-ones normalization without increasing either indexed width

The formulas are the all-ones directional model. The existing exact diagonal
asymptotic identity proves its all-input equality; no derivative-existence
or pre-normalized-network hypothesis is imported.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators
variable {N h₁ h₂ : ℕ}

noncomputable def positiveLinear (net : ZNet N h₁ h₂) (k : Fin h₂) : Point N :=
  ∑ j, if 0 < net.s j then net.W k j • net.A j else 0

noncomputable def fromZ (net : ZNet N h₁ h₂) : NormalizedNetwork N h₁ h₂ where
  A j := if net.s j = 0 then net.A j else 0
  U k := if net.Tp k = 0 then positiveLinear net k else 0
  W k j := if net.Tp k = 0 ∧ net.s j = 0 then net.W k j else 0
  L := ∑ k, if 0 < net.Tp k then net.d k • positiveLinear net k else 0
  B j := if net.s j = 0 then ∑ k, if 0 < net.Tp k then net.d k * net.W k j else 0 else 0
  d k := if net.Tp k = 0 then net.d k else 0

/-- The original first covector is retained exactly, or replaced by zero. -/
theorem fromZ_first_row (net : ZNet N h₁ h₂) (j : Fin h₁) :
    (fromZ net).A j = if net.s j = 0 then net.A j else 0 := rfl

theorem fromZ_support_subset (net : ZNet N h₁ h₂) (j : Fin h₁) :
    rowSupport ((fromZ net).A j) ⊆ rowSupport (net.A j) := by
  classical
  by_cases hj : net.s j = 0
  · simp only [fromZ,hj,ite_true]
    exact Finset.Subset.refl _
  · simp [fromZ,hj,rowSupport]

/-- Deleting outer slots and first forms cannot create a new feeding index. -/
theorem fromZ_feeding_original (net : ZNet N h₁ h₂) (j : Fin h₁)
    (hj : (fromZ net).Feeding j) : ∃ k, net.W k j ≠ 0 := by
  obtain ⟨k,hk⟩ := hj
  refine ⟨k,?_⟩
  by_contra hz
  exact hk (by simp [fromZ,hz])

lemma lin_positiveLinear (net : ZNet N h₁ h₂) (k : Fin h₂) (x : Point N) :
    lin (positiveLinear net k) x =
      ∑ j, if 0 < net.s j then net.W k j * lin (net.A j) x else 0 := by
  classical
  rw [positiveLinear,lin_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [lin_smul_left,lin_zero_left]

lemma sum_positiveLinear (net : ZNet N h₁ h₂) (k : Fin h₂) :
    (∑ i, positiveLinear net k i) = net.Tp k := by
  classical
  have he := lin_positiveLinear net k (diag 1)
  rw [lin_diag,one_mul] at he
  rw [he]
  unfold ZNet.Tp
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : 0 < net.s j <;> simp [hj,lin_diag,pick,ZNet.s]

/-- The first local derivative splits into its linear and invariant-ReLU parts. -/
lemma gp_decomposition (net : ZNet N h₁ h₂) (k : Fin h₂) (x : Point N) :
    net.Gp k x = lin (positiveLinear net k) x +
      ∑ j, net.W k j * relu (lin ((fromZ net).A j) x) := by
  classical
  rw [lin_positiveLinear,← Finset.sum_add_distrib]
  unfold ZNet.Gp
  apply Finset.sum_congr rfl
  intro j _
  by_cases hp : 0 < net.s j
  · have hz : net.s j ≠ 0 := ne_of_gt hp
    simp [pick,hp,hz,fromZ,lin_zero_left,relu]
  · by_cases hz : net.s j = 0
    · simp [pick,hp,hz,fromZ]
    · have hn : net.s j < 0 := by
        rcases lt_trichotomy (net.s j) 0 with h | h | h
        · exact h
        · exact False.elim (hz h)
        · exact False.elim (hp h)
      simp [pick,hp,hz,hn,fromZ,lin_zero_left,relu]

lemma fromZ_inner (net : ZNet N h₁ h₂) (k : Fin h₂) (x : Point N) :
    (fromZ net).inner k x = if net.Tp k = 0 then net.Gp k x else 0 := by
  classical
  by_cases hk : net.Tp k = 0
  · rw [if_pos hk,gp_decomposition]
    have hU : (fromZ net).U k = positiveLinear net k := by simp [fromZ,hk]
    rw [inner,hU]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : net.s j = 0 <;> simp [fromZ,hk,hj,lin_zero_left,relu]
  · simp [inner,fromZ,hk,lin_zero_left,relu]

lemma fromZ_linear_output (net : ZNet N h₁ h₂) (x : Point N) :
    lin (fromZ net).L x + (∑ j, (fromZ net).B j * relu (lin ((fromZ net).A j) x)) =
      ∑ k, if 0 < net.Tp k then net.d k * net.Gp k x else 0 := by
  classical
  have hlin : lin (fromZ net).L x =
      ∑ k, if 0 < net.Tp k then net.d k * lin (positiveLinear net k) x else 0 := by
    change lin (∑ k, if 0 < net.Tp k then net.d k • positiveLinear net k else 0) x = _
    rw [lin_sum_left]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp [lin_smul_left,lin_zero_left]
  have hfirst : (∑ j, (fromZ net).B j * relu (lin ((fromZ net).A j) x)) =
      ∑ k, if 0 < net.Tp k then net.d k *
        (∑ j, net.W k j * relu (lin ((fromZ net).A j) x)) else 0 := by
    calc
      _ = ∑ j, ∑ k, if 0 < net.Tp k then net.d k * net.W k j *
          relu (lin ((fromZ net).A j) x) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : net.s j = 0
        · simp only [fromZ,hj,ite_true,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          split_ifs <;> ring
        · simp [fromZ,hj,lin_zero_left,relu]
      _ = ∑ k, ∑ j, if 0 < net.Tp k then net.d k * net.W k j *
          relu (lin ((fromZ net).A j) x) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : 0 < net.Tp k <;> simp [hk,Finset.mul_sum,mul_assoc]
  rw [hlin,hfirst,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 0 < net.Tp k
  · rw [if_pos hk,if_pos hk,if_pos hk,gp_decomposition]
    ring
  · simp [hk]

/-- Exact evaluation identity, before imposing any target function. -/
theorem fromZ_eval (net : ZNet N h₁ h₂) (x : Point N) :
    (fromZ net).eval x = net.rest x := by
  classical
  rw [eval,fromZ_linear_output,← Finset.sum_add_distrib]
  unfold ZNet.rest
  apply Finset.sum_congr rfl
  intro k _
  rw [fromZ_inner]
  by_cases hp : 0 < net.Tp k
  · have hz : net.Tp k ≠ 0 := ne_of_gt hp
    simp [fromZ,pick,hp,hz]
  · by_cases hz : net.Tp k = 0
    · simp [fromZ,pick,hp,hz]
    · have hn : net.Tp k < 0 := by
        rcases lt_trichotomy (net.Tp k) 0 with h | h | h
        · exact h
        · exact False.elim (hz h)
        · exact False.elim (hp h)
      simp [fromZ,pick,hp,hz,hn]

/-- Every exact bias-free MAX network has the same exact indexed skip model. -/
theorem fromZ_computes_max [NeZero N] (net : ZNet N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    ∀ x, (fromZ net).eval x = Maximum N x := by
  intro x
  rw [fromZ_eval]
  exact ((net.max_plus hnet).2 x).symm

lemma fromZ_output_sum (net : ZNet N h₁ h₂) :
    (∑ i, (fromZ net).L i) = net.slope := by
  classical
  have he : (∑ i, (fromZ net).L i) = lin (fromZ net).L (diag 1) := by
    rw [lin_diag,one_mul]
  rw [he]
  change lin (∑ k, if 0 < net.Tp k then net.d k • positiveLinear net k else 0) (diag 1) = _
  rw [lin_sum_left]
  unfold ZNet.slope
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 0 < net.Tp k
  · rw [if_pos hk,lin_smul_left,lin_diag,one_mul,sum_positiveLinear]
    simp [pick,hk]
  · simp [hk,pick,lin_zero_left]

/-- Both first rows and outer linear skips are translation invariant; the
linear output has the target's unit diagonal slope. -/
theorem fromZ_translation_normalized [NeZero N] (net : ZNet N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    (fromZ net).TranslationNormalized := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro j
    by_cases hj : net.s j = 0
    · change (∑ i, (if net.s j = 0 then net.A j else 0) i) = 0
      rw [if_pos hj]
      exact hj
    · simp [fromZ,hj]
  · intro k
    by_cases hk : net.Tp k = 0
    · simpa only [fromZ,hk,ite_true,sum_positiveLinear] using hk
    · simp [fromZ,hk]
  · rw [fromZ_output_sum]
    exact (net.max_plus hnet).1

#check @fromZ_computes_max
#print axioms fromZ_computes_max
#print axioms fromZ_translation_normalized

end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
