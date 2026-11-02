import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.Ordinary
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.SwitchingRows

/-! # Choose the physical positive-atom order before constructing its path -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment

noncomputable def swapLeadingAtoms (net : Network 4 6 5)
    (e : Fin 3 ≃ NetworkAtoms net) : Fin 3 ≃ NetworkAtoms net :=
  (Equiv.swap 0 1).trans e

lemma swapLeadingAtoms_zero (net : Network 4 6 5) (e : Fin 3 ≃ NetworkAtoms net) :
    swapLeadingAtoms net e 0=e 1 := congrArg e (by decide)
lemma swapLeadingAtoms_one (net : Network 4 6 5) (e : Fin 3 ≃ NetworkAtoms net) :
    swapLeadingAtoms net e 1=e 0 := congrArg e (by decide)
lemma swapLeadingAtoms_two (net : Network 4 6 5) (e : Fin 3 ≃ NetworkAtoms net) :
    swapLeadingAtoms net e 2=e 2 := congrArg e (by decide)

lemma swapLeadingAtoms_jumps (net : Network 4 6 5) (e : Fin 3 ≃ NetworkAtoms net)
    (hj : ∀ i,networkAtomJump net (e i)=(![1,1,-1] : Fin 3 → ℝ) i) :
    ∀ i,networkAtomJump net (swapLeadingAtoms net e i)=(![1,1,-1] : Fin 3 → ℝ) i := by
  intro i
  fin_cases i
  · change networkAtomJump net (swapLeadingAtoms net e 0)=1
    rw [swapLeadingAtoms_zero]
    exact hj 1
  · change networkAtomJump net (swapLeadingAtoms net e 1)=1
    rw [swapLeadingAtoms_one]
    exact hj 0
  · change networkAtomJump net (swapLeadingAtoms net e 2) = -1
    rw [swapLeadingAtoms_two]
    exact hj 2

lemma swapLeadingAtoms_offsets (net : Network 4 6 5) (U : Fin 2 → Fin 2 → ℝ)
    (e : Fin 3 ≃ NetworkAtoms net)
    (hoff : ∀ a b,networkAtomOffset net U a b (e 0)*networkAtomOffset net U a b (e 1)=0 ∧
      networkAtomOffset net U a b (e 2)=
        networkAtomOffset net U a b (e 0)+networkAtomOffset net U a b (e 1)) :
    ∀ a b,networkAtomOffset net U a b (swapLeadingAtoms net e 0)*
      networkAtomOffset net U a b (swapLeadingAtoms net e 1)=0 ∧
      networkAtomOffset net U a b (swapLeadingAtoms net e 2)=
        networkAtomOffset net U a b (swapLeadingAtoms net e 0)+
          networkAtomOffset net U a b (swapLeadingAtoms net e 1) := by
  intro a b
  rw [swapLeadingAtoms_zero,swapLeadingAtoms_one,swapLeadingAtoms_two]
  exact ⟨(mul_comm _ _).trans (hoff a b).1,(hoff a b).2.trans (add_comm _ _)⟩

/-- Either ordering the two positive physical atoms gives a directly
contractible profile, or precisely the exceptional orientation remains. -/
theorem switching_order_cases (net : Network 4 6 5) (U : Fin 2 → Fin 2 → ℝ)
    (e : Fin 3 ≃ NetworkAtoms net)
    (hj : ∀ i,networkAtomJump net (e i)=(![1,1,-1] : Fin 3 → ℝ) i)
    (hoff : ∀ a b,networkAtomOffset net U a b (e 0)*networkAtomOffset net U a b (e 1)=0 ∧
      networkAtomOffset net U a b (e 2)=
        networkAtomOffset net U a b (e 0)+networkAtomOffset net U a b (e 1)) :
    (∃ f : Fin 3 ≃ NetworkAtoms net,
      (∀ i,networkAtomJump net (f i)=(![1,1,-1] : Fin 3 → ℝ) i) ∧
      (∀ a b,networkAtomOffset net U a b (f 0)*networkAtomOffset net U a b (f 1)=0 ∧
        networkAtomOffset net U a b (f 2)=
          networkAtomOffset net U a b (f 0)+networkAtomOffset net U a b (f 1)) ∧
      networkAtomFlip net (f 0)=networkAtomFlip net (f 2)) ∨
    (networkAtomFlip net (e 0)=networkAtomFlip net (e 1) ∧
      networkAtomFlip net (e 0)≠networkAtomFlip net (e 2)) := by
  rcases orientation_cases (networkAtomFlip net (e 0))
    (networkAtomFlip net (e 1)) (networkAtomFlip net (e 2)) with h | h | h
  · exact Or.inl ⟨e,hj,hoff,h⟩
  · refine Or.inl ⟨swapLeadingAtoms net e,swapLeadingAtoms_jumps net e hj,
      swapLeadingAtoms_offsets net U e hoff,?_⟩
    rw [swapLeadingAtoms_zero,swapLeadingAtoms_two]
    exact h
  · exact Or.inr h

#print axioms switching_order_cases
end MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
