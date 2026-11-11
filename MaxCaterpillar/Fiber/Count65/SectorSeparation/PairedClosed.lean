import MaxCaterpillar.Fiber.Count65.SectorSeparation.PairedReconstruction
import MaxCaterpillar.Fiber.First65.Irredundancy
import MaxCaterpillar.Fiber.Mixed65.SectorNormalForm

/-! Relative closedness of the full paired sector, with arbitrary biases and
suffix weights. The independent-code condition follows from exactness. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.SectorSeparation

noncomputable def pairedLabeled : Set (ExactFiber 4 6 5) :=
  {net | LabeledPairedRows net.val.W₁}

lemma pairedLabeled_iff_closedRows (net : ExactFiber 4 6 5) :
    net ∈ pairedLabeled ↔ PairedClosedRows net.val.W₁ := by
  constructor
  · exact pairedClosedRows_of_labeled
  · intro h
    apply labeled_of_pairedClosedRows net.val.W₁ ?_ ?_ h
    · intro j hz
      obtain ⟨i,hi⟩ := net.val.first_row_ne_zero_of_max4_six net.property j
      exact hi (congrFun hz i)
    · intro j k hjk t ht
      exact net.val.first_rows_not_pos_proportional_of_max4_six net.property hjk ht

lemma isClosed_pairedLabeled : IsClosed pairedLabeled := by
  have heq : pairedLabeled = {net : ExactFiber 4 6 5 | PairedClosedRows net.val.W₁} := by
    ext net
    exact pairedLabeled_iff_closedRows net
  rw [heq]
  exact isClosed_pairedClosedRows.preimage (continuous_W₁.comp continuous_subtype_val)

lemma paired_eq_iUnion :
    {net : ExactFiber 4 6 5 | PairedFirstMatrixForm net.val} =
      ⋃ p : Equiv.Perm (Fin 6), ⋃ q : Equiv.Perm (Fin 4),
        Mixed65.permutationHomeomorph p q '' pairedLabeled := by
  ext net
  constructor
  · rintro ⟨a,b,c,d,hd,s,hs,p,q,hrows⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
    refine ⟨(Mixed65.permutationHomeomorph p q).symm net, ?_,
      (Mixed65.permutationHomeomorph p q).apply_symm_apply net⟩
    refine ⟨a,b,c,d,hd,(fun j => s (p.symm j)),(fun j => hs (p.symm j)),?_⟩
    funext j i
    rw [Mixed65.permutationHomeomorph_symm_W₁,hrows]
    simp only [Equiv.apply_symm_apply]
  · intro hn
    obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hn
    obtain ⟨q,b,⟨a,c,d,e,hd,s,hs,hrows⟩,hb⟩ := Set.mem_iUnion.mp hp
    subst net
    refine ⟨a,c,d,e,hd,(fun j => s (p j)),(fun j => hs (p j)),p,q,?_⟩
    intro j i
    rw [Mixed65.permutationHomeomorph_W₁]
    exact congrFun (congrFun hrows (p j)) (q i)

/-- The paired-code sector is closed in the complete physical exact fiber.
Every bias and every suffix weight is unrestricted. -/
theorem isClosed_pairedFirstMatrixForm :
    IsClosed {net : ExactFiber 4 6 5 | PairedFirstMatrixForm net.val} := by
  rw [paired_eq_iUnion]
  apply isClosed_iUnion_of_finite
  intro p
  apply isClosed_iUnion_of_finite
  intro q
  exact (Mixed65.permutationHomeomorph p q).isClosedMap _ isClosed_pairedLabeled

#print axioms isClosed_pairedFirstMatrixForm
end MaxCaterpillar.Fiber.Count65.SectorSeparation
