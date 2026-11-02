import MaxCaterpillar.Fiber.Count65.SectorQuotient.FrameRigidity
import MaxCaterpillar.Fiber.Count65.SectorQuotient.NormalizedSecond

/-! The actual full symmetry relation on canonical unit-output mixed/star
frames identifies precisely second-hidden-neuron permutations. No additional
normalization or functional equivalence is used as a generator. -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

/-- Exact orbit characterization for canonical mixed physical networks. -/
theorem mixed_normalized_symmetry_iff (a b : ExactFiber 4 6 5)
    (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (ha : a.val.W₁=Mixed65.firstRows t) (hb : b.val.W₁=Mixed65.firstRows u)
    (haunit : ∀ k,a.val.w₃ k=1 ∨ a.val.w₃ k = -1)
    (hbunit : ∀ k,b.val.w₃ k=1 ∨ b.val.w₃ k = -1) :
    EqvGen SymmetryStep a b ↔
      t=u ∧ ∃ p : Equiv.Perm (Fin 5),b.val=permuteHidden a.val (Equiv.refl _) p := by
  constructor
  · intro h
    obtain ⟨w⟩ := physicalOrbit_of_symmetry h
    have hframe : ∀ j i,Mixed65.firstRows u j i=
        w.s₁ j*Mixed65.firstRows t (w.p₁ j) (w.q i) := by
      intro j i
      simpa only [ha,hb] using w.first_weights j i
    have hr := mixed_frame_rigidity u t hu ht w.s₁ w.positive₁ w.p₁ w.q hframe
    exact ⟨hr.1.symm,w.p₂,eq_second_permute_of_trivial_first w hr.2.1 hr.2.2.1
      hr.2.2.2 haunit hbunit⟩
  · rintro ⟨_,p,hp⟩
    exact symmetry_of_eq_second_permute p hp

/-- The star endpoint introduces no extra identification in the full genuine
symmetry quotient. All biases remain arbitrary in this statement. -/
theorem star_normalized_symmetry_iff (a b : ExactFiber 4 6 5)
    (t u : ℝ) (ht : 0<t) (ht1 : t≤1) (hu : 0<u) (hu1 : u≤1)
    (ha : a.val.W₁=Star65.firstRows t) (hb : b.val.W₁=Star65.firstRows u)
    (haunit : ∀ k,a.val.w₃ k=1 ∨ a.val.w₃ k = -1)
    (hbunit : ∀ k,b.val.w₃ k=1 ∨ b.val.w₃ k = -1) :
    EqvGen SymmetryStep a b ↔
      t=u ∧ ∃ p : Equiv.Perm (Fin 5),b.val=permuteHidden a.val (Equiv.refl _) p := by
  constructor
  · intro h
    obtain ⟨w⟩ := physicalOrbit_of_symmetry h
    have hframe : ∀ j i,Star65.firstRows u j i=
        w.s₁ j*Star65.firstRows t (w.p₁ j) (w.q i) := by
      intro j i
      simpa only [ha,hb] using w.first_weights j i
    have hr := star_frame_rigidity u t hu hu1 ht ht1 w.s₁ w.positive₁ w.p₁ w.q hframe
    exact ⟨hr.1.symm,w.p₂,eq_second_permute_of_trivial_first w hr.2.1 hr.2.2.1
      hr.2.2.2 haunit hbunit⟩
  · rintro ⟨_,p,hp⟩
    exact symmetry_of_eq_second_permute p hp

#print axioms mixed_normalized_symmetry_iff
#print axioms star_normalized_symmetry_iff
end MaxCaterpillar.Fiber.Count65.SectorQuotient
