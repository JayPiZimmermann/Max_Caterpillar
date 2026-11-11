import MaxCaterpillar.Fiber.GatingAbstractions.Defs
import MaxCaterpillar.Fiber.NaturalInterventions

/-!
# Equal complete gating maps with different representation partitions

The examples are ordinary minimal-width, bias-free Max4 networks. Every gate,
including its zero status, agrees on every real input. Nevertheless their second
hidden representation partitions are incomparable. Smoothness of the full
normalized fiber is a separate local-completeness claim, not inferred from the
continuous family in this file.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.GatingAbstractions
open BigOperators Frontier

variable {N h₁ h₂ : ℕ}

/-- The first physical preactivation, before its ReLU. -/
noncomputable def firstPre (net : Network N h₁ h₂) (x : Point N) (j : Fin h₁) : ℝ :=
  (∑ i, net.W₁ j i * x i) + net.b₁ j

/-- The second physical preactivation, using the actual first hidden state. -/
noncomputable def secondPre (net : Network N h₁ h₂) (x : Point N) (k : Fin h₂) : ℝ :=
  (∑ j, net.W₂ k j * net.firstHidden x j) + net.b₂ k

/-- Equality of all three sign statuses at every gate and every input. -/
def SameCompleteGates (net net' : Network N h₁ h₂) : Prop :=
  (∀ x j, SameSign (firstPre net x j) (firstPre net' x j)) ∧
    (∀ x k, SameSign (secondPre net x k) (secondPre net' x k))

lemma family_firstHidden (c : ℝ) (x : Point 4) :
    (family c).firstHidden x = pairedFeatures x := by
  change (NaturalInterventions.net 0).firstHidden x = pairedFeatures x
  simpa only [pairedFeatures] using NaturalInterventions.firstHidden_net 0 x

lemma family_firstPre (c : ℝ) (x : Point 4) :
    (fun j => firstPre (family c) x j) =
      ![x 0-x 1,x 2-x 3,x 1,-x 1,x 3,-x 3] := by
  funext j
  fin_cases j <;>
    simp [firstPre, family, splitNet, pairedNet, maxFourNet,
      Fin.sum_univ_succ, sub_eq_add_neg] <;> rfl

lemma firstPre_inputX (c : ℝ) :
    (fun j => firstPre (family c) inputX j) = ![1,2,1,-1,1,-1] := by
  rw [family_firstPre]
  change ![2-1,3-1,1,-1,1,-1] = _
  norm_num

lemma firstPre_inputY (c : ℝ) :
    (fun j => firstPre (family c) inputY j) = ![1/2,2,3/2,-3/2,1,-1] := by
  rw [family_firstPre]
  change ![2-3/2,3-1,3/2,-(3/2),1,-1] = _
  norm_num

lemma firstPre_inputZ (c : ℝ) :
    (fun j => firstPre (family c) inputZ j) = ![1/2,2,2,-2,1,-1] := by
  rw [family_firstPre]
  change ![5/2-2,3-1,2,-2,1,-1] = _
  norm_num

lemma firstPre_inputW (c : ℝ) :
    (fun j => firstPre (family c) inputW j) = ![4,2,1,-1,1,-1] := by
  rw [family_firstPre]
  change ![5-1,3-1,1,-1,1,-1] = _
  norm_num

lemma family_zeroBiases (c : ℝ) : (family c).HasZeroBiases := ⟨rfl,rfl,rfl⟩

lemma first_row_pos (c : ℝ) (hc : 0 < c) (j : Fin 6) :
    0 < (family c).W₂ 0 j := by
  fin_cases j <;> simp [family, splitNet, pairedNet, offset] <;> exact hc

lemma second_row_pos (c : ℝ) (hc : 0 < c) (j : Fin 6) :
    0 < (family c).W₂ 1 j := by
  fin_cases j <;> simp [family, splitNet, pairedNet, offset] <;> exact hc

private lemma weighted_zero_iff {ι : Type*} [Fintype ι] (a z : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hz : ∀ i, 0 ≤ z i) :
    (∑ i, a i * z i) = 0 ↔ ∀ i, z i = 0 := by
  classical
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (ha i).le (hz i))]
  constructor
  · intro h i
    exact (mul_eq_zero.mp (h i (Finset.mem_univ i))).resolve_left (ha i).ne'
  · intro h i _
    rw [h i, mul_zero]

private lemma positive_rows_sameSign {ι : Type*} [Fintype ι]
    (a b z : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hz : ∀ i, 0 ≤ z i) : SameSign (∑ i, a i*z i) (∑ i, b i*z i) := by
  apply sameSign_of_nonneg
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (ha i).le (hz i)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hb i).le (hz i)
  · rw [weighted_zero_iff a z ha hz, weighted_zero_iff b z hb hz]

/-- The full all-input gate maps agree, including all boundary gates. -/
theorem family_same_complete_gates (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    SameCompleteGates (family c) (family d) := by
  constructor
  · intro x j
    exact sameSign_refl _
  · intro x k
    fin_cases k
    · unfold secondPre
      rw [family_firstHidden, family_firstHidden]
      simp only [family, splitNet, pairedNet, Pi.zero_apply, add_zero]
      exact positive_rows_sameSign _ _ _ (first_row_pos c hc) (first_row_pos d hd)
        (pairedFeatures_nonneg x)
    · unfold secondPre
      rw [family_firstHidden, family_firstHidden]
      simp only [family, splitNet, pairedNet, Pi.zero_apply, add_zero]
      exact positive_rows_sameSign _ _ _ (second_row_pos c hc) (second_row_pos d hd)
        (pairedFeatures_nonneg x)
    · exact sameSign_refl _

lemma secondPre_inputX (c : ℝ) :
    (fun k => secondPre (family c) inputX k) = ![c+7,c+4,-1] := by
  funext k
  unfold secondPre
  rw [family_firstHidden, pairedFeatures_inputX]
  fin_cases k <;>
    norm_num [family, splitNet, pairedNet, offset, pairedFeatures,
      pairedOuterCoefficients, Fin.sum_univ_succ, relu] <;> ring

lemma secondPre_inputY (c : ℝ) :
    (fun k => secondPre (family c) inputY k) = ![c/2+15/2,c/2+9/2,-1] := by
  funext k
  unfold secondPre
  rw [family_firstHidden, pairedFeatures_inputY]
  fin_cases k <;>
    norm_num [family, splitNet, pairedNet, offset, pairedFeatures,
      pairedOuterCoefficients, Fin.sum_univ_succ, relu] <;> ring

lemma secondPre_inputZ (c : ℝ) :
    (fun k => secondPre (family c) inputZ k) = ![c/2+8,c/2+5,-1/2] := by
  funext k
  unfold secondPre
  rw [family_firstHidden, pairedFeatures_inputZ]
  fin_cases k <;>
    norm_num [family, splitNet, pairedNet, offset, pairedFeatures,
      pairedOuterCoefficients, Fin.sum_univ_succ, relu] <;> ring

lemma secondPre_inputW (c : ℝ) :
    (fun k => secondPre (family c) inputW k) = ![4*c+7,4*c+4,2] := by
  funext k
  unfold secondPre
  rw [family_firstHidden, pairedFeatures_inputW]
  fin_cases k <;>
    norm_num [family, splitNet, pairedNet, offset, pairedFeatures,
      pairedOuterCoefficients, Fin.sum_univ_succ, relu] <;> ring

lemma secondHidden_inputX (c : ℝ) (hc : 0 ≤ c) :
    (family c).secondHidden inputX = ![c+7,c+4,0] := by
  change (fun k => relu (secondPre (family c) inputX k)) = _
  funext k
  rw [show secondPre (family c) inputX k = _ from congrFun (secondPre_inputX c) k]
  fin_cases k
  · change relu (c+7) = c+7
    exact relu_of_nonneg (by linarith)
  · change relu (c+4) = c+4
    exact relu_of_nonneg (by linarith)
  · change relu (-1) = 0
    exact relu_of_nonpos (by norm_num)

lemma secondHidden_inputY (c : ℝ) (hc : 0 ≤ c) :
    (family c).secondHidden inputY = ![c/2+15/2,c/2+9/2,0] := by
  change (fun k => relu (secondPre (family c) inputY k)) = _
  funext k
  rw [show secondPre (family c) inputY k = _ from congrFun (secondPre_inputY c) k]
  fin_cases k
  · change relu (c/2+15/2) = c/2+15/2
    exact relu_of_nonneg (by linarith)
  · change relu (c/2+9/2) = c/2+9/2
    exact relu_of_nonneg (by linarith)
  · change relu (-1) = 0
    exact relu_of_nonpos (by norm_num)

lemma secondHidden_inputZ (c : ℝ) (hc : 0 ≤ c) :
    (family c).secondHidden inputZ = ![c/2+8,c/2+5,0] := by
  change (fun k => relu (secondPre (family c) inputZ k)) = _
  funext k
  rw [show secondPre (family c) inputZ k = _ from congrFun (secondPre_inputZ c) k]
  fin_cases k
  · change relu (c/2+8) = c/2+8
    exact relu_of_nonneg (by linarith)
  · change relu (c/2+5) = c/2+5
    exact relu_of_nonneg (by linarith)
  · change relu (-1/2) = 0
    exact relu_of_nonpos (by norm_num)

/-- The first merger occurs at an interior positive parameter. -/
theorem mergeXY_iff (c : ℝ) (hc : 0 ≤ c) :
    (family c).secondHidden inputX = (family c).secondHidden inputY ↔ c = 1 := by
  rw [secondHidden_inputX c hc, secondHidden_inputY c hc]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h0
    linarith
  · intro h
    subst c
    norm_num

/-- A different pair merges at a different interior parameter. -/
theorem mergeXZ_iff (c : ℝ) (hc : 0 ≤ c) :
    (family c).secondHidden inputX = (family c).secondHidden inputZ ↔ c = 2 := by
  rw [secondHidden_inputX c hc, secondHidden_inputZ c hc]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h0
    linarith
  · intro h
    subst c
    norm_num

/-- Passive representation refinement: every collision of H remains a collision of K. -/
def Refines {X Y Z : Type*} (H : X → Y) (K : X → Z) : Prop :=
  ∀ x y, H x = H y → K x = K y

/-- The two partitions are incomparable despite identical complete gating maps. -/
theorem family_partitions_incomparable :
    ¬ Refines (family 1).secondHidden (family 2).secondHidden ∧
      ¬ Refines (family 2).secondHidden (family 1).secondHidden := by
  constructor
  · intro h
    have hm := h inputX inputY ((mergeXY_iff 1 (by norm_num)).mpr rfl)
    have he := (mergeXY_iff 2 (by norm_num)).mp hm
    norm_num at he
  · intro h
    have hm := h inputX inputZ ((mergeXZ_iff 2 (by norm_num)).mpr rfl)
    have he := (mergeXZ_iff 1 (by norm_num)).mp hm
    norm_num at he

/-- A continuous path of exact networks passes through both merger events. -/
theorem continuous_exact_segment :
    Continuous (fun t : ℝ => family (1+t)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, (family (1+t)).eval x = Maximum 4 x := by
  constructor
  · exact continuous_family.comp (continuous_const.add continuous_id)
  · intro t ht x
    exact family_eval _ (by linarith [ht.1]) x

/-- No recoding of one attained representation can recover the other. -/
theorem no_representation_recoding :
    (¬ ∃ Q : (Fin 3 → ℝ) → (Fin 3 → ℝ),
      ∀ x, (family 2).secondHidden x = Q ((family 1).secondHidden x)) ∧
    (¬ ∃ Q : (Fin 3 → ℝ) → (Fin 3 → ℝ),
      ∀ x, (family 1).secondHidden x = Q ((family 2).secondHidden x)) := by
  constructor
  · rintro ⟨Q,hQ⟩
    apply family_partitions_incomparable.1
    intro x y h
    rw [hQ x, hQ y, h]
  · rintro ⟨Q,hQ⟩
    apply family_partitions_incomparable.2
    intro x y h
    rw [hQ x, hQ y, h]

/-- The two concrete all-input exact fiber points. -/
noncomputable def oneExact : ExactFiber 4 6 3 := ⟨family 1,family_eval 1 (by norm_num)⟩
noncomputable def twoExact : ExactFiber 4 6 3 := ⟨family 2,family_eval 2 (by norm_num)⟩

open unitInterval

/-- Both merge events lie on this explicit path in the full exact fiber. -/
noncomputable def exactPath : Path oneExact twoExact where
  toFun t := ⟨family (1+(t : ℝ)),family_eval _ (by linarith [t.property.1])⟩
  continuous_toFun :=
    (continuous_family.comp (continuous_const.add continuous_subtype_val)).subtype_mk _
  source' := by
    apply Subtype.ext
    change family (1+(0 : ℝ)) = family 1
    rw [add_zero]
  target' := by
    apply Subtype.ext
    change family (1+(1 : ℝ)) = family 2
    norm_num

/-- The complete gating map remains fixed along the whole physical path. -/
theorem exactPath_gates_fixed (s t : I) :
    SameCompleteGates (exactPath s).val (exactPath t).val := by
  apply family_same_complete_gates
  · linarith [s.property.1]
  · linarith [t.property.1]

/-- The two representations occur in one path component of the full exact fiber. -/
theorem exact_points_joined : Joined oneExact twoExact := ⟨exactPath⟩

/-- The explicit counterexample combines all-input exactness, equal complete
sign maps, and incomparable second-hidden-layer representation partitions. -/
theorem same_gates_different_representations :
    (∀ x, (family 1).eval x = Maximum 4 x) ∧
    (∀ x, (family 2).eval x = Maximum 4 x) ∧
    SameCompleteGates (family 1) (family 2) ∧
    ¬ Refines (family 1).secondHidden (family 2).secondHidden ∧
    ¬ Refines (family 2).secondHidden (family 1).secondHidden :=
  ⟨family_eval 1 (by norm_num), family_eval 2 (by norm_num),
    family_same_complete_gates 1 2 (by norm_num) (by norm_num),
    family_partitions_incomparable⟩

end MaxCaterpillar.Fiber.GatingAbstractions
