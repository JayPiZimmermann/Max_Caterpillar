import MaxCaterpillar.Fiber.Count65.ActualFirstMatrix
import MaxCaterpillar.Fiber.Count65.SectorSeparation
import MaxCaterpillar.Fiber.Disconnected65
import MaxCaterpillar.Fiber.Count65.SectorQuotient.PairedDisjoint
import MaxCaterpillar.Fiber.Count65.SectorQuotient.MixedStarDisjoint

/-! The three actual first-matrix sectors form an invariant clopen partition
of the complete biased exact Max4(6,5) fiber. Exhaustion is a proved theorem
about actual networks, rather than a classification hypothesis. -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

/-- The actual independent paired-code sector, with arbitrary suffix and biases. -/
def pairedSet : Set (ExactFiber 4 6 5) := {net | PairedFirstMatrixForm net.val}

/-- The actual positive-path/star sector, including its parameter-one endpoint. -/
def starSet : Set (ExactFiber 4 6 5) := {net | StarFirstMatrixForm net.val}

theorem paired_mixed_disjoint : Disjoint pairedSet Mixed65.sector := by
  apply Set.disjoint_left.mpr
  intro net hp hm
  exact not_paired_of_mixedFirstMatrixForm net.val
    ((Mixed65.mem_sector_iff_firstMatrixForm net).mp hm) hp

theorem paired_star_disjoint : Disjoint pairedSet starSet := by
  apply Set.disjoint_left.mpr
  intro net hp hs
  exact not_paired_of_starFirstMatrixForm net.val hs hp

theorem mixed_star_disjoint : Disjoint Mixed65.sector starSet := by
  apply Set.disjoint_left.mpr
  intro net hm hs
  exact not_star_of_mixedFirstMatrixForm net.val
    ((Mixed65.mem_sector_iff_firstMatrixForm net).mp hm) hs

theorem sectors_pairwise_disjoint :
    Disjoint pairedSet Mixed65.sector ∧ Disjoint pairedSet starSet ∧
      Disjoint Mixed65.sector starSet :=
  ⟨paired_mixed_disjoint,paired_star_disjoint,mixed_star_disjoint⟩

/-- Every actual exact network belongs to one of the three disjoint sectors. -/
theorem sector_union_univ : pairedSet ∪ Mixed65.sector ∪ starSet = Set.univ := by
  apply Set.eq_univ_of_forall
  intro net
  rcases max4_first_matrix_trichotomy net.val net.property with hp | hm | hs
  · exact Or.inl (Or.inl hp)
  · exact Or.inl (Or.inr ((Mixed65.mem_sector_iff_firstMatrixForm net).mpr hm))
  · exact Or.inr hs

theorem paired_compl_eq : pairedSetᶜ = Mixed65.sector ∪ starSet := by
  ext net
  constructor
  · intro h
    rcases max4_first_matrix_trichotomy net.val net.property with hp | hm | hs
    · exact (h hp).elim
    · exact Or.inl ((Mixed65.mem_sector_iff_firstMatrixForm net).mpr hm)
    · exact Or.inr hs
  · rintro (hm | hs) hp
    · exact Set.disjoint_left.mp paired_mixed_disjoint hp hm
    · exact Set.disjoint_left.mp paired_star_disjoint hp hs

theorem star_compl_eq : starSetᶜ = pairedSet ∪ Mixed65.sector := by
  ext net
  constructor
  · intro h
    rcases max4_first_matrix_trichotomy net.val net.property with hp | hm | hs
    · exact Or.inl hp
    · exact Or.inr ((Mixed65.mem_sector_iff_firstMatrixForm net).mpr hm)
    · exact (h hs).elim
  · rintro (hp | hm) hs
    · exact Set.disjoint_left.mp paired_star_disjoint hp hs
    · exact Set.disjoint_left.mp mixed_star_disjoint hm hs

theorem pairedSector_isClosed : IsClosed pairedSet := isClosed_pairedFirstMatrixForm

theorem starSector_isClosed : IsClosed starSet := isClosed_starFirstMatrixForm

/-- The paired sector is clopen in the complete actual biased exact fiber. -/
theorem pairedSector_isClopen : IsClopen pairedSet := by
  refine ⟨?_,pairedSector_isClosed⟩
  have hc : IsClosed pairedSetᶜ := by
    rw [paired_compl_eq]
    exact max4_6_5_mixed_sector_isClopen.2.union starSector_isClosed
  simpa only [compl_compl] using hc.isOpen_compl

/-- The complete star sector is clopen, including its canonical endpoint. -/
theorem starSector_isClopen : IsClopen starSet := by
  refine ⟨?_,starSector_isClosed⟩
  have hc : IsClosed starSetᶜ := by
    rw [star_compl_eq]
    exact pairedSector_isClosed.union max4_6_5_mixed_sector_isClopen.2
  simpa only [compl_compl] using hc.isOpen_compl

theorem pairedSet_symmetryInvariant : SymmetryInvariant pairedSet :=
  pairedFirstMatrixForm_symmetryInvariant

theorem starSet_symmetryInvariant : SymmetryInvariant starSet :=
  starFirstMatrixForm_symmetryInvariant

end MaxCaterpillar.Fiber.Count65.SectorQuotient
