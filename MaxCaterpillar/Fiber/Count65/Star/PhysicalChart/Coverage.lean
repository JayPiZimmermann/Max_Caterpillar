import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Extraction

/-! # Every actual star normal form belongs to a canonical physical chart

The chart inverse retains the original physical coefficients. Coverage is an
equality of all six parameter arrays after a genuine hidden permutation and
bias retraction, rather than an equality of realized functions.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65

private lemma network_ext {a b : Network 4 6 5}
    (h1 : a.W₁=b.W₁) (h2 : a.b₁=b.b₁) (h3 : a.W₂=b.W₂)
    (h4 : a.b₂=b.b₂) (h5 : a.w₃=b.w₃) (h6 : a.b₃=b.b₃) : a=b := by
  cases a
  cases b
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  rfl

lemma normalFormPermutation_core {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) (i : Fin 3) :
    normalFormPermutation F (Fin.castAdd 2 i)=(F.order i).val := by
  have he := normalFormPermutation_spec F
  fin_cases i
  · exact he.1
  · exact he.2.1
  · exact he.2.2.1

lemma orderedPhysicalNet_core_row {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) (i : Fin 3) :
    (orderedPhysicalNet F).W₂ (Fin.castAdd 2 i)=
      extendRow (coefficientRow (F.core.reindex F.order) i) 0 0 := by
  funext j
  change net.W₂ (normalFormPermutation F (Fin.castAdd 2 i)) j=_
  rw [normalFormPermutation_core F i]
  have hc := F.original_coefficients (F.order i)
  have hs := F.stationary (F.order i).val (F.order i).property
  fin_cases j
  · change net.W₂ (F.order i).val 0=(F.core.reindex F.order).U i
    exact hc.2.1.symm
  · change net.W₂ (F.order i).val 1=(F.core.reindex F.order).V i
    exact hc.2.2.1.symm
  · change net.W₂ (F.order i).val 2=(F.core.reindex F.order).W i
    exact hc.2.2.2.1.symm
  · change net.W₂ (F.order i).val 3=(F.core.reindex F.order).T i
    exact hc.2.2.2.2.symm
  · exact hs.1
  · exact hs.2

lemma unscale_orientedRow (r : ℝ) (b : Bool) (a : Fin 4→ℝ) :
    unscaleCoefficients r (orientedRow b a)=
      fun n => orientation b*unscaleCoefficients r a n := by
  funext n
  fin_cases n
  · change (orientation b*a 0)/r=orientation b*(a 0/r)
    simp only [div_eq_mul_inv]
    ring
  · rfl
  · rfl
  · change (orientation b*a 3)/r=orientation b*(a 3/r)
    simp only [div_eq_mul_inv]
    ring

/-- Exact inverse of all six physical parameter arrays once the three core
rows have been recovered. No additional normalization is inserted. -/
theorem headLift_eq_orderedPhysicalNet {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) (hr : 0<r) (hW : net.W₁=firstRows r)
    (C : Fin 3→Fin 4→ℝ)
    (hrows : ∀ i,coefficientRow (F.core.reindex F.order) i=unscaleCoefficients r (C i)) :
    headLift r (C 0) (C 1) (C 2) (extractedHeads F)=orderedPhysicalNet F := by
  have hp := normalFormPermutation_spec F
  have hA : unscaleCoefficients r (recoverReadout 1 (extractedHeads F).2.1)=
      originalHeadRow net F.positiveHead := by
    change unscaleCoefficients r
      (recoverReadout 1 (coefficientReadout 1
        (scaleCoefficients r (originalHeadRow net F.positiveHead))))=_
    rw [recover_coefficientReadout (by norm_num : (0:ℝ)<1),unscale_scaleCoefficients hr]
  have hB : unscaleCoefficients r (recoverReadout 1 (extractedHeads F).2.2)=
      originalHeadRow net F.negativeHead := by
    change unscaleCoefficients r
      (recoverReadout 1 (coefficientReadout 1
        (scaleCoefficients r (originalHeadRow net F.negativeHead))))=_
    rw [recover_coefficientReadout (by norm_num : (0:ℝ)<1),unscale_scaleCoefficients hr]
  apply network_ext
  · exact hW.symm
  · rfl
  · funext k
    fin_cases k
    · change extendRow (unscaleCoefficients r (C 0)) 0 0=(orderedPhysicalNet F).W₂ 0
      rw [← hrows 0]
      exact (orderedPhysicalNet_core_row F 0).symm
    · change extendRow (unscaleCoefficients r (C 1)) 0 0=(orderedPhysicalNet F).W₂ 1
      rw [← hrows 1]
      exact (orderedPhysicalNet_core_row F 1).symm
    · change extendRow (unscaleCoefficients r (C 2)) 0 0=(orderedPhysicalNet F).W₂ 2
      rw [← hrows 2]
      exact (orderedPhysicalNet_core_row F 2).symm
    · change extendRow (unscaleCoefficients r (recoverReadout 1 (extractedHeads F).2.1))
        (net.W₂ F.positiveHead 4) (net.W₂ F.positiveHead 5)=
        fun j => net.W₂ (normalFormPermutation F 3) j
      rw [hA,hp.2.2.2.1]
      funext j
      fin_cases j <;> rfl
    · change extendRow (unscaleCoefficients r (recoverReadout 1 (extractedHeads F).2.2))
        (net.W₂ F.negativeHead 4) (net.W₂ F.negativeHead 5)=
        fun j => net.W₂ (normalFormPermutation F 4) j
      rw [hB,hp.2.2.2.2]
      funext j
      fin_cases j <;> rfl
  · rfl
  · funext k
    fin_cases k
    · change (1:ℝ)=net.w₃ (normalFormPermutation F 0)
      rw [hp.1,← (F.original_coefficients (F.order 0)).1]
      exact F.positive_first.symm
    · change (1:ℝ)=net.w₃ (normalFormPermutation F 1)
      rw [hp.2.1,← (F.original_coefficients (F.order 1)).1]
      exact F.positive_second.symm
    · change (-1:ℝ)=net.w₃ (normalFormPermutation F 2)
      rw [hp.2.2.1,← (F.original_coefficients (F.order 2)).1]
      exact F.negative_third.symm
    · change (1:ℝ)=net.w₃ (normalFormPermutation F 3)
      rw [hp.2.2.2.1]
      exact F.positive_output.symm
    · change (-1:ℝ)=net.w₃ (normalFormPermutation F 4)
      rw [hp.2.2.2.2]
      exact F.negative_output.symm
  · rfl

lemma rowForm_oriented_remainder (r i j z : ℝ) (C : Fin 3→Fin 4→ℝ) (q v w : ℝ) :
    rowForm r (fun n => (![0,0,1,0] : Fin 4→ℝ) n+i*C 0 n+j*C 1 n-z*C 2 n) q v w=
      max 0 w+i*rowForm r (C 0) q v w+j*rowForm r (C 1) q v w-z*rowForm r (C 2) q v w := by
  change (0+i*C 0 0+j*C 1 0-z*C 2 0)*max 0 q+
    (0+i*C 0 1+j*C 1 1-z*C 2 1)*max 0 v+
    (1+i*C 0 2+j*C 1 2-z*C 2 2)*max 0 w+
    (0+i*C 0 3+j*C 1 3-z*C 2 3)*max 0 (q+r*v)=_
  unfold rowForm starLinearForm
  ring

lemma rowForm_unscale_at_scaled {r : ℝ} (hr : 0<r) (a : Fin 4→ℝ) (q v w : ℝ) :
    rowForm r (unscaleCoefficients r a) (r*q) v w=
      (coefficientReadout 1 a : InvariantState→ℝ) (q,v,w) := by
  have he := unscaleCoefficients_readout hr a (r*q) v w
  have hq : (r*q)/r=q := by field_simp [ne_of_gt hr]; ring
  change rowForm r (unscaleCoefficients r a) (r*q) v w=_ at he
  rwa [hq] at he

/-- The inverse head data reconstructs the canonical invariant remainder
whenever the exact recovered original core rows match the selected chart. -/
theorem extractedHeads_reconstructs_of_rows {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) (hr : 0<r) (C : Fin 3→Fin 4→ℝ)
    (hrows : ∀ i,coefficientRow (F.core.reindex F.order) i=
      fun n => (-(F.core.reindex F.order).W i)*unscaleCoefficients r (C i) n)
    (L : featureSpace 1)
    (hL : ∀ x : InvariantState,(L : InvariantState→ℝ) x=
      max 0 x.2.2+flipValue (coreOrientation F 0)*
        (coefficientReadout 1 (C 0) : InvariantState→ℝ) x+
      flipValue (coreOrientation F 1)*(coefficientReadout 1 (C 1) : InvariantState→ℝ) x-
      flipValue (coreOrientation F 2)*(coefficientReadout 1 (C 2) : InvariantState→ℝ) x) :
    (HeadTopology.toHeads (extractedHeads F)).Reconstructs (L : InvariantState→ℝ) := by
  have hb := base_row_oriented (F.core.reindex F.order) hr F.corrected_remainder
    (fun i => unscaleCoefficients r (C i)) hrows (unit_core_W F)
    F.positive_first F.positive_second F.negative_third
  intro x z
  rcases x with ⟨q,v,w⟩
  rw [extractedHeads_eval F hr,F.head_identity]
  have he := congrArg (fun a : Fin 4→ℝ => rowForm r a (r*q) v w) hb
  dsimp only at he
  rw [rowForm_oriented_remainder r _ _ _ (fun i => unscaleCoefficients r (C i)),
    rowForm_unscale_at_scaled hr,
    rowForm_unscale_at_scaled hr,rowForm_unscale_at_scaled hr] at he
  change starBase F.core r (r*q) v w=_ at he
  rw [← coreOrientation_flipValue F 0,← coreOrientation_flipValue F 1,
    ← coreOrientation_flipValue F 2] at he
  change z+starBase F.core r (r*q) v w=z+(L : InvariantState→ℝ) (q,v,w)
  rw [he,← hL (q,v,w)]

/-- Every derived actual physical normal form is a canonical branch chart
network after the genuine core/head permutation and bias retraction. -/
theorem physical_normal_form_covered {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) (hr : 0<r) (hr1 : r≤1) (hW : net.W₁=firstRows r) :
    (∃ p : BranchIFiber (coreOrientation F),
      branchIChart (coreOrientation F) p=orderedPhysicalNet F) ∨
    (∃ p : BranchIIFiber (coreOrientation F),
      branchIIChart (coreOrientation F) p=orderedPhysicalNet F) := by
  have hw : ∀ i,(F.core.reindex F.order).W i≠0 := by
    intro i
    rcases unit_core_W F i with he | he <;> rw [he] <;> norm_num
  obtain ⟨hu0,ht0,ht1,hv1⟩ := F.carrier_relations
  rcases F.branches with ⟨hh,hk,hn,hm,hl⟩ | ⟨hk,hh,hn,hm,hl⟩
  · let b : ResidualBase 0 := ⟨(r,normalizedK (F.core.reindex F.order)),hr,hr1,hk⟩
    have hrow := branchI_rows_recovered (F.core.reindex F.order) hr hw
      hu0 ht0 ht1 hv1 hh hn hm hl
    have hrows : ∀ i,coefficientRow (F.core.reindex F.order) i=
        fun n => (-(F.core.reindex F.order).W i)*unscaleCoefficients r (coreRowsI b i) n := by
      intro i
      rw [hrow i,branchIRows_eq_unscale b i]
    have hheads := extractedHeads_reconstructs_of_rows F hr (coreRowsI b) hrows
      (coefficientReadout 1 (branchICoefficients (flipValue (coreOrientation F 0))
        (flipValue (coreOrientation F 1)) (flipValue (coreOrientation F 2)) b))
      (branchI_remainder_readout _ _ _ b)
    let p : BranchIFiber (coreOrientation F) := ⟨(b,extractedHeads F),hheads⟩
    refine Or.inl ⟨p,?_⟩
    apply headLift_eq_orderedPhysicalNet F hr hW (fun i => orientedRow (coreOrientation F i) (coreRowsI b i))
    intro i
    rw [unscale_orientedRow,← coreOrientation_factor F i]
    exact hrows i
  · let b : ResidualBase (-1) := ⟨(r,normalizedH (F.core.reindex F.order)),hr,hr1,hh⟩
    have hrow := branchII_rows_recovered (F.core.reindex F.order) hr hw
      hu0 ht0 ht1 hv1 hk hn hm hl
    have hrows : ∀ i,coefficientRow (F.core.reindex F.order) i=
        fun n => (-(F.core.reindex F.order).W i)*unscaleCoefficients r (coreRowsII b i) n := by
      intro i
      rw [hrow i,branchIIRows_eq_unscale b i]
    have hheads := extractedHeads_reconstructs_of_rows F hr (coreRowsII b) hrows
      (coefficientReadout 1 (branchIICoefficients (flipValue (coreOrientation F 0))
        (flipValue (coreOrientation F 1)) (flipValue (coreOrientation F 2)) b))
      (branchII_remainder_readout _ _ _ b)
    let p : BranchIIFiber (coreOrientation F) := ⟨(b,extractedHeads F),hheads⟩
    refine Or.inr ⟨p,?_⟩
    apply headLift_eq_orderedPhysicalNet F hr hW (fun i => orientedRow (coreOrientation F i) (coreRowsII b i))
    intro i
    rw [unscale_orientedRow,← coreOrientation_factor F i]
    exact hrows i

/-- Coverage starts from an arbitrary exact physical network, with all original
biases permitted. Its normal-form certificate is a conclusion, not a hypothesis. -/
theorem actual_star_network_covered (net : Network 4 6 5) (r : ℝ)
    (hr : 0<r) (hr1 : r≤1) (hW : net.W₁=firstRows r)
    (hmax : ∀ x,net.eval x=Maximum 4 x) :
    ∃ F : PhysicalNormalForm (PhysicalExtraction.normalizeSecond net) r,
      (∃ p : BranchIFiber (coreOrientation F),
        branchIChart (coreOrientation F) p=orderedPhysicalNet F) ∨
      (∃ p : BranchIIFiber (coreOrientation F),
        branchIIChart (coreOrientation F) p=orderedPhysicalNet F) := by
  obtain ⟨F⟩ := exists_physical_normal_form net r hr hr1 hW hmax
  exact ⟨F,physical_normal_form_covered F hr hr1 hW⟩
end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
