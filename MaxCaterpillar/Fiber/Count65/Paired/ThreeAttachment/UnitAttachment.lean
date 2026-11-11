import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment.Unit
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.UnitWitness
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.RawOrdinary

/-! # Attach the actual unit-comparison witnesses produced by three atoms -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment

lemma oriented_comparison_natural (U : Fin 2 → Fin 2 → ℝ) (row : Fin 6 → ℝ)
    (flip : Bool) (hrow : row=(if flip then -comparisonRow U else comparisonRow U)) :
    ∀ x,endpointForm U row x=
      if flip then -endpointForm U (comparisonRow U) x else endpointForm U (comparisonRow U) x := by
  intro x
  rw [hrow]
  cases flip
  · rfl
  · exact endpointForm_neg U (comparisonRow U) x

theorem literal_unit_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U≠0)
    (hW : a.val.W₁=pairedRows U) (hb : a.val.HasZeroBiases)
    (c : Fin 5) (flip : Bool) (hout : a.val.w₃ c=1)
    (hrow : a.val.W₂ c=(if flip then -comparisonRow U else comparisonRow U)) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) :=
  LowAtomsAttachment.unit_comparison_quotient_joined a U hdet hW hb c flip hout
    (oriented_comparison_natural U (a.val.W₂ c) flip hrow)

/-- The global unit-label alternative derived from arbitrary three-atom
exactness attaches without assuming a unit slope in the source. -/
theorem global_unit_atom_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U≠0)
    (hW : a.val.W₁=pairedRows U) (hb : a.val.HasZeroBiases) (i : NetworkAtoms a.val)
    (hj : networkAtomJump a.val i=1) (hoff : ∀ u v,networkAtomOffset a.val U u v i=0) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  obtain ⟨n,hnW,hnb,hnout,hnrow,hnpath⟩ :=
    global_unit_atom_witness a.val U hdet hW hb a.property i hj hoff
  exact (joinedIn_exact_quotient a n hnpath).trans
    (literal_unit_quotient_joined n U hdet hnW hnb i.val (networkAtomFlip a.val i) hnout hnrow)

theorem ordinary_switching_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U≠0)
    (hW : a.val.W₁=pairedRows U) (hb : a.val.HasZeroBiases)
    (e : Fin 3 ≃ NetworkAtoms a.val)
    (hj : ∀ i,networkAtomJump a.val (e i)=(![1,1,-1] : Fin 3 → ℝ) i)
    (hoff : ∀ u v,networkAtomOffset a.val U u v (e 0)*networkAtomOffset a.val U u v (e 1)=0 ∧
      networkAtomOffset a.val U u v (e 2)=
        networkAtomOffset a.val U u v (e 0)+networkAtomOffset a.val U u v (e 1))
    (hflip : networkAtomFlip a.val (e 0)=networkAtomFlip a.val (e 2)) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  obtain ⟨n,hnW,hnb,hnout,hnrow,hnpath⟩ :=
    raw_ordinary_switching_to_unit a.val U hdet hW hb a.property e hj hoff hflip
  exact hnpath.trans
    (literal_unit_quotient_joined n U hdet hnW hnb 0 (networkAtomFlip a.val (e 0)) hnout hnrow)

#print axioms global_unit_atom_quotient_joined
#print axioms ordinary_switching_quotient_joined
end MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
