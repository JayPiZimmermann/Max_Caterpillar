import MaxCaterpillar.Fiber.Count65.Mixed.PhysicalNormalForm

/-! # Uniqueness of the actual mixed physical roles

Head and core roles are characterized by actual output signs, translation
supports and invariant incoming coefficients. Thus choosing an existential
normal-form certificate introduces no new discrete freedom.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open MaxCaterpillar.Frontier

namespace PhysicalNormalForm
variable {net : Network 4 6 5} {t : ℝ}

noncomputable def coreIndex (r : PhysicalNormalForm net t) (i : Fin 3) : Fin 5 :=
  (r.order i).val
noncomputable def remainder (r : PhysicalNormalForm net t) : InvariantState → ℝ :=
  fun x => r.core.base t x.1 x.2.1 x.2.2

lemma ordered_out (r : PhysicalNormalForm net t) (i : Fin 3) :
    (r.core.reindex r.order).out i = net.w₃ (r.coreIndex i) :=
  (r.original_coefficients (r.order i)).1
lemma ordered_U (r : PhysicalNormalForm net t) (i : Fin 3) :
    (r.core.reindex r.order).U i = net.W₂ (r.coreIndex i) 0 :=
  (r.original_coefficients (r.order i)).2.1
lemma ordered_V (r : PhysicalNormalForm net t) (i : Fin 3) :
    (r.core.reindex r.order).V i = net.W₂ (r.coreIndex i) 1 :=
  (r.original_coefficients (r.order i)).2.2.1
lemma ordered_W (r : PhysicalNormalForm net t) (i : Fin 3) :
    (r.core.reindex r.order).W i = net.W₂ (r.coreIndex i) 2 :=
  (r.original_coefficients (r.order i)).2.2.2.1
lemma ordered_T (r : PhysicalNormalForm net t) (i : Fin 3) :
    (r.core.reindex r.order).T i = net.W₂ (r.coreIndex i) 3 :=
  (r.original_coefficients (r.order i)).2.2.2.2

lemma core_output_zero (r : PhysicalNormalForm net t) : net.w₃ (r.coreIndex 0) = 1 := by
  rw [← r.ordered_out 0]
  exact r.positive_first
lemma core_output_one (r : PhysicalNormalForm net t) : net.w₃ (r.coreIndex 1) = 1 := by
  rw [← r.ordered_out 1]
  exact r.positive_second
lemma core_output_two (r : PhysicalNormalForm net t) : net.w₃ (r.coreIndex 2) = -1 := by
  rw [← r.ordered_out 2]
  exact r.negative_third

lemma core_W_ne_zero (r : PhysicalNormalForm net t) (i : Fin 3) :
    net.W₂ (r.coreIndex i) 2 ≠ 0 := by
  have hw := r.orientations i
  rw [r.ordered_W i] at hw
  split_ifs at hw <;> rw [hw] <;> norm_num

lemma core_left_U (r : PhysicalNormalForm net t) :
    net.W₂ (r.coreIndex 0) 0 = -(1+t)*net.W₂ (r.coreIndex 0) 2 := by
  rw [← r.ordered_U 0,← r.ordered_W 0]
  rcases r.branches with ⟨k,_,hd⟩ | ⟨s,_,hd⟩ <;> exact hd.1

lemma core_right_U (r : PhysicalNormalForm net t) :
    net.W₂ (r.coreIndex 1) 0 = -net.W₂ (r.coreIndex 1) 2 := by
  rw [← r.ordered_U 1,← r.ordered_W 1]
  rcases r.branches with ⟨k,_,hd⟩ | ⟨s,_,hd⟩ <;> exact hd.2.2.2.1

lemma core_stationary (r : PhysicalNormalForm net t) (i : Fin 3) :
    net.W₂ (r.coreIndex i) 4 = 0 ∧ net.W₂ (r.coreIndex i) 5 = 0 :=
  r.stationary _ (r.order i).property

lemma positiveHead_carrier (r : PhysicalNormalForm net t) : 0 < net.W₂ r.positiveHead 4 :=
  halfLine_first_slope_pos _ _ _ _ _
    (r.head_identity.positive_halfLine ((0 : ℝ),0,0))
lemma negativeHead_carrier (r : PhysicalNormalForm net t) : 0 < net.W₂ r.negativeHead 5 :=
  halfLine_first_slope_pos _ _ _ _ _
    (r.head_identity.negative_halfLine ((0 : ℝ),0,0))

lemma stationary_mem_core (r : PhysicalNormalForm net t) (j : Fin 5)
    (h4 : net.W₂ j 4 = 0) (h5 : net.W₂ j 5 = 0) :
    j ∈ coreIndices r.positiveHead r.negativeHead := by
  classical
  have hp : j ≠ r.positiveHead := by
    intro he
    rw [he] at h4
    exact r.positiveHead_carrier.ne' h4
  have hn : j ≠ r.negativeHead := by
    intro he
    rw [he] at h5
    exact r.negativeHead_carrier.ne' h5
  exact Finset.mem_erase.mpr ⟨hn,Finset.mem_erase.mpr ⟨hp,Finset.mem_univ _⟩⟩

lemma positiveHead_unique (r s : PhysicalNormalForm net t) : r.positiveHead = s.positiveHead := by
  classical
  by_contra hne
  have hneg : s.positiveHead ≠ r.negativeHead := by
    intro he
    have hp := s.positive_output
    rw [he,r.negative_output] at hp
    norm_num at hp
  have hmem : s.positiveHead ∈ coreIndices r.positiveHead r.negativeHead :=
    Finset.mem_erase.mpr ⟨hneg,Finset.mem_erase.mpr ⟨Ne.symm hne,Finset.mem_univ _⟩⟩
  exact s.positiveHead_carrier.ne' (r.stationary _ hmem).1

lemma negativeHead_unique (r s : PhysicalNormalForm net t) : r.negativeHead = s.negativeHead := by
  classical
  by_contra hne
  have hpos : s.negativeHead ≠ r.positiveHead := by
    intro he
    have hn := s.negative_output
    rw [he,r.positive_output] at hn
    norm_num at hn
  have hmem : s.negativeHead ∈ coreIndices r.positiveHead r.negativeHead :=
    Finset.mem_erase.mpr ⟨Ne.symm hne,Finset.mem_erase.mpr ⟨hpos,Finset.mem_univ _⟩⟩
  exact s.negativeHead_carrier.ne' (r.stationary _ hmem).2

lemma core_left_unique (r : PhysicalNormalForm net t) (ht : 0 < t) (j : Fin 5)
    (hout : net.w₃ j = 1) (h4 : net.W₂ j 4 = 0) (h5 : net.W₂ j 5 = 0)
    (hu : net.W₂ j 0 = -(1+t)*net.W₂ j 2) : j = r.coreIndex 0 := by
  classical
  obtain ⟨i,hi⟩ := r.order.surjective ⟨j,r.stationary_mem_core j h4 h5⟩
  have hij : r.coreIndex i = j := congrArg Subtype.val hi
  fin_cases i
  · exact hij.symm
  · change r.coreIndex 1 = j at hij
    have hr := r.core_right_U
    have hw := r.core_W_ne_zero 1
    rw [hij] at hr hw
    have hz : t*net.W₂ j 2 = 0 := by nlinarith only [hu,hr]
    exact False.elim ((mul_ne_zero ht.ne' hw) hz)
  · change r.coreIndex 2 = j at hij
    have hn := r.core_output_two
    rw [hij,hout] at hn
    norm_num at hn

lemma core_right_unique (r : PhysicalNormalForm net t) (ht : 0 < t) (j : Fin 5)
    (hout : net.w₃ j = 1) (h4 : net.W₂ j 4 = 0) (h5 : net.W₂ j 5 = 0)
    (hu : net.W₂ j 0 = -net.W₂ j 2) : j = r.coreIndex 1 := by
  classical
  obtain ⟨i,hi⟩ := r.order.surjective ⟨j,r.stationary_mem_core j h4 h5⟩
  have hij : r.coreIndex i = j := congrArg Subtype.val hi
  fin_cases i
  · change r.coreIndex 0 = j at hij
    have hl := r.core_left_U
    have hw := r.core_W_ne_zero 0
    rw [hij] at hl hw
    have hz : t*net.W₂ j 2 = 0 := by nlinarith only [hu,hl]
    exact False.elim ((mul_ne_zero ht.ne' hw) hz)
  · exact hij.symm
  · change r.coreIndex 2 = j at hij
    have hn := r.core_output_two
    rw [hij,hout] at hn
    norm_num at hn

lemma core_negative_unique (r : PhysicalNormalForm net t) (j : Fin 5)
    (hout : net.w₃ j = -1) (h4 : net.W₂ j 4 = 0) (h5 : net.W₂ j 5 = 0) :
    j = r.coreIndex 2 := by
  classical
  obtain ⟨i,hi⟩ := r.order.surjective ⟨j,r.stationary_mem_core j h4 h5⟩
  have hij : r.coreIndex i = j := congrArg Subtype.val hi
  fin_cases i
  · change r.coreIndex 0 = j at hij
    have hp := r.core_output_zero
    rw [hij,hout] at hp
    norm_num at hp
  · change r.coreIndex 1 = j at hij
    have hp := r.core_output_one
    rw [hij,hout] at hp
    norm_num at hp
  · exact hij.symm

/-- Every certificate chooses the same three original physical core indices. -/
theorem coreIndex_unique (r s : PhysicalNormalForm net t) (ht : 0 < t) :
    ∀ i, r.coreIndex i = s.coreIndex i := by
  intro i
  fin_cases i
  · exact (r.core_left_unique ht _ s.core_output_zero
      (s.core_stationary 0).1 (s.core_stationary 0).2 s.core_left_U).symm
  · exact (r.core_right_unique ht _ s.core_output_one
      (s.core_stationary 1).1 (s.core_stationary 1).2 s.core_right_U).symm
  · exact (r.core_negative_unique _ s.core_output_two
      (s.core_stationary 2).1 (s.core_stationary 2).2).symm

/-- The two branch labels have a finite closed coordinate description. -/
lemma branch_markers_exhaustive (r : PhysicalNormalForm net t) :
    net.W₂ (r.coreIndex 0) 1 = 0 ∨ net.W₂ (r.coreIndex 1) 3 = 0 := by
  rw [← r.ordered_V 0,← r.ordered_T 1]
  rcases r.branches with ⟨k,_,hd⟩ | ⟨s,_,hd⟩
  · exact Or.inl hd.2.1
  · exact Or.inr hd.2.2.2.2.2.1

/-- The two closed branch descriptions never meet, including chart endpoints. -/
lemma branch_markers_disjoint (r : PhysicalNormalForm net t) (ht : 0 < t) :
    ¬ (net.W₂ (r.coreIndex 0) 1 = 0 ∧ net.W₂ (r.coreIndex 1) 3 = 0) := by
  rintro ⟨hv,hT⟩
  rcases r.branches with ⟨k,hk,hd⟩ | ⟨s,hs,hd⟩
  · have hkpos : 0 < k := by
      by_contra hn
      have hn := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hn)
      linarith only [hk,hn]
    have he := hd.2.2.2.2.2.1
    rw [r.ordered_T 1,r.ordered_W 1,hT] at he
    exact (mul_ne_zero hkpos.ne' (r.core_W_ne_zero 1)) he.symm
  · have hspos : 0 < s := by
      by_contra hn
      have hn := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hn)
      linarith only [ht,hs,hn]
    have he := hd.2.1
    rw [r.ordered_V 0,r.ordered_W 0,hv] at he
    exact (mul_ne_zero hspos.ne' (r.core_W_ne_zero 0)) he.symm

lemma branch_marker_unique (r s : PhysicalNormalForm net t) (ht : 0 < t) :
    (net.W₂ (r.coreIndex 0) 1 = 0) ↔ (net.W₂ (s.coreIndex 0) 1 = 0) := by
  rw [r.coreIndex_unique s ht 0]

lemma coreIndex_injective (r : PhysicalNormalForm net t) : Function.Injective r.coreIndex := by
  intro i j he
  exact r.order.injective (Subtype.ext he)

lemma coreIndex_ne_positiveHead (r : PhysicalNormalForm net t) (i : Fin 3) :
    r.coreIndex i ≠ r.positiveHead :=
  (Finset.mem_erase.mp (Finset.mem_erase.mp (r.order i).property).2).1
lemma coreIndex_ne_negativeHead (r : PhysicalNormalForm net t) (i : Fin 3) :
    r.coreIndex i ≠ r.negativeHead :=
  (Finset.mem_erase.mp (r.order i).property).1

noncomputable def roleOrderFunction (r : PhysicalNormalForm net t) : Fin 5 → Fin 5 :=
  ![r.coreIndex 0,r.coreIndex 1,r.coreIndex 2,r.positiveHead,r.negativeHead]

lemma roleOrderFunction_injective (r : PhysicalNormalForm net t) :
    Function.Injective r.roleOrderFunction := by
  have h01 := r.coreIndex_injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := r.coreIndex_injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := r.coreIndex_injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have h03 := r.coreIndex_ne_positiveHead 0
  have h13 := r.coreIndex_ne_positiveHead 1
  have h23 := r.coreIndex_ne_positiveHead 2
  have h04 := r.coreIndex_ne_negativeHead 0
  have h14 := r.coreIndex_ne_negativeHead 1
  have h24 := r.coreIndex_ne_negativeHead 2
  have h34 := r.heads_distinct
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp [roleOrderFunction,h01,h02,h12,h03,h13,h23,h04,h14,h24,h34,
      Ne.symm h01,Ne.symm h02,Ne.symm h12,Ne.symm h03,Ne.symm h13,Ne.symm h23,
      Ne.symm h04,Ne.symm h14,Ne.symm h24,Ne.symm h34] at he ⊢

/-- The five canonical roles enumerate every original physical neuron. -/
noncomputable def roleOrder (r : PhysicalNormalForm net t) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective r.roleOrderFunction
    ⟨r.roleOrderFunction_injective,Finite.surjective_of_injective r.roleOrderFunction_injective⟩

@[simp] lemma roleOrder_core (r : PhysicalNormalForm net t) (i : Fin 3) :
    r.roleOrder (Fin.castAdd 2 i) = r.coreIndex i := by
  fin_cases i <;> rfl
@[simp] lemma roleOrder_positiveHead (r : PhysicalNormalForm net t) :
    r.roleOrder 3 = r.positiveHead := rfl
@[simp] lemma roleOrder_negativeHead (r : PhysicalNormalForm net t) :
    r.roleOrder 4 = r.negativeHead := rfl

lemma roleOrder_unique (r s : PhysicalNormalForm net t) (ht : 0 < t) :
    r.roleOrder = s.roleOrder := by
  apply Equiv.ext
  intro i
  fin_cases i
  · exact r.coreIndex_unique s ht 0
  · exact r.coreIndex_unique s ht 1
  · exact r.coreIndex_unique s ht 2
  · exact r.positiveHead_unique s
  · exact r.negativeHead_unique s

lemma remainder_unique (r s : PhysicalNormalForm net t) : r.remainder = s.remainder := by
  funext x
  have hr := r.head_identity x 0
  have hs := s.head_identity x 0
  change _ = 0+r.remainder x at hr
  change _ = 0+s.remainder x at hs
  rw [r.positiveHead_unique s,r.negativeHead_unique s] at hr
  linarith only [hr,hs]

lemma orientation_unique (r s : PhysicalNormalForm net t) (ht : 0 < t) (i : Fin 3) :
    ((r.core.reindex r.order).W i < 0) ↔ ((s.core.reindex s.order).W i < 0) := by
  rw [r.ordered_W,s.ordered_W,r.coreIndex_unique s ht i]

lemma signed_kind_unique (r s : PhysicalNormalForm net t) :
    (actualHeads net t r.positiveHead r.negativeHead).IsSigned r.remainder ↔
      (actualHeads net t s.positiveHead s.negativeHead).IsSigned s.remainder := by
  rw [r.positiveHead_unique s,r.negativeHead_unique s,r.remainder_unique s]

end PhysicalNormalForm
end MaxCaterpillar.Fiber.Mixed65
