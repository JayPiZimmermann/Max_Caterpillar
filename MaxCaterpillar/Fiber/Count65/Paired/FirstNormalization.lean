import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.Count65.Paired.CodeOffsets
import MaxCaterpillar.Fiber.BiasQuotient

/-! # Normalize every actual paired first matrix by genuine allowed symmetries

Positive first-neuron scales and the stated hidden/input permutations produce
exactly pairedRows U with det U nonzero. The six-array network and all suffix
coefficients are transported by the actual symmetry maps; no first-matrix
classification condition is assumed for the second layer.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired

/-- Every zero-bias representative of the actual paired sector has a normalized
representative with arbitrary invertible code in the same genuine quotient. -/
theorem paired_normalized_representative (x : ZeroBiasFiber 4 6 5)
    (h : PairedFirstMatrixForm x.val.val) :
    ∃ U : Fin 2 → Fin 2 → ℝ, codeDet U≠0 ∧
      ∃ y : ZeroBiasFiber 4 6 5, y.val.val.W₁=pairedRows U ∧
        Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x=
          Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) y := by
  classical
  obtain ⟨a,b,c,d,had,s,hs,p,q,hrows⟩ := h
  let U : Fin 2 → Fin 2 → ℝ := ![![a,b],![c,d]]
  have hdet : codeDet U≠0 := by simpa [U,codeDet] using had
  let invs : Fin 6 → ℝ := fun j => (s j)⁻¹
  have hpos : ∀ j, 0<invs j := fun j => inv_pos.mpr (hs j)
  let scaled := scaleFirstFiber invs hpos x.val
  let hidden := permuteHiddenFiber p.symm (Equiv.refl _) scaled
  let normal := permuteInputsFiber q.symm hidden
  have hfirst : normal.val.W₁=pairedRows U := by
    funext j i
    change (s (p.symm j))⁻¹*x.val.val.W₁ (p.symm j) (q.symm i)=pairedRows U j i
    rw [hrows]
    simp only [p.apply_symm_apply,q.apply_symm_apply]
    rw [← mul_assoc,inv_mul_cancel (ne_of_gt (hs (p.symm j))),one_mul]
    rfl
  have hzero : normal.val.HasZeroBiases := by
    rcases x.property with ⟨hb1,hb2,hb3⟩
    refine ⟨?_,?_,?_⟩
    · funext j
      change (s (p.symm j))⁻¹*x.val.val.b₁ (p.symm j)=0
      rw [hb1]
      simp
    · funext k
      change x.val.val.b₂ k=0
      rw [hb2]
      rfl
    · change x.val.val.b₃=0
      exact hb3
  let y : ZeroBiasFiber 4 6 5 := ⟨normal,hzero⟩
  refine ⟨U,hdet,y,hfirst,?_⟩
  apply Quotient.sound
  change EqvGen SymmetryStep x.val normal
  exact EqvGen.trans _ _ _
    (EqvGen.rel _ _ (SymmetryStep.first x.val invs hpos))
    (EqvGen.trans _ _ _
      (EqvGen.rel _ _ (SymmetryStep.hidden scaled p.symm (Equiv.refl _)))
      (EqvGen.rel _ _ (SymmetryStep.input hidden q.symm)))

end MaxCaterpillar.Fiber.Count65.Paired
