import MaxCaterpillar.Fiber.Count65.SectorQuotient.PhysicalOrbit

/-! Unit output magnitudes remove all remaining second-neuron rescalings.
The conclusion is equality of complete physical networks, including biases. -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

lemma unit_output_scale (a b s : ℝ) (hs : 0<s)
    (ha : a=1 ∨ a = -1) (hb : b=1 ∨ b = -1) (h : b=a/s) : s=1 := by
  have hmul : b*s=a := (eq_div_iff hs.ne').mp h
  rcases ha with ha|ha <;> rcases hb with hb|hb <;>
    rw [ha,hb] at hmul <;> nlinarith only [hmul,hs]

variable {N h₁ h₂ : ℕ}

/-- Once first-frame rigidity has been proved, a genuine physical orbit
between unit-output networks consists solely of a second-neuron permutation. -/
theorem eq_second_permute_of_trivial_first {a b : Network N h₁ h₂}
    (w : PhysicalOrbitWitness a b)
    (hp : w.p₁=Equiv.refl _) (hq : w.q=Equiv.refl _)
    (hs : ∀ j,w.s₁ j=1)
    (ha : ∀ k,a.w₃ k=1 ∨ a.w₃ k = -1)
    (hb : ∀ k,b.w₃ k=1 ∨ b.w₃ k = -1) :
    b=permuteHidden a (Equiv.refl _) w.p₂ := by
  have ht : ∀ k,w.s₂ k=1 := fun k =>
    unit_output_scale _ _ _ (w.positive₂ k) (ha (w.p₂ k)) (hb k) (w.output_weights k)
  apply (networkEquivParameters N h₁ h₂).injective
  have hW₁ : b.W₁=(permuteHidden a (Equiv.refl _) w.p₂).W₁ := by
    funext j i
    simpa only [hp,hq,hs,Equiv.refl_apply,one_mul,permuteHidden] using w.first_weights j i
  have hb₁ : b.b₁=(permuteHidden a (Equiv.refl _) w.p₂).b₁ := by
    funext j
    simpa only [hp,hs,Equiv.refl_apply,one_mul,permuteHidden] using w.first_bias j
  have hW₂ : b.W₂=(permuteHidden a (Equiv.refl _) w.p₂).W₂ := by
    funext k j
    simpa only [hp,hs,ht,Equiv.refl_apply,one_mul,div_one,permuteHidden] using w.second_weights k j
  have hb₂ : b.b₂=(permuteHidden a (Equiv.refl _) w.p₂).b₂ := by
    funext k
    simpa only [ht,one_mul,permuteHidden] using w.second_bias k
  have hw₃ : b.w₃=(permuteHidden a (Equiv.refl _) w.p₂).w₃ := by
    funext k
    simpa only [ht,div_one,permuteHidden] using w.output_weights k
  exact Prod.ext hW₁ (Prod.ext hb₁ (Prod.ext hW₂ (Prod.ext hb₂
    (Prod.ext hw₃ w.output_bias))))

variable [NeZero N]

lemma symmetry_of_eq_second_permute {a b : ExactFiber N h₁ h₂}
    (p : Equiv.Perm (Fin h₂)) (h : b.val=permuteHidden a.val (Equiv.refl _) p) :
    EqvGen SymmetryStep a b := by
  have hb : b=permuteHiddenFiber (Equiv.refl _) p a := Subtype.ext h
  rw [hb]
  exact EqvGen.rel _ _ (SymmetryStep.hidden a (Equiv.refl _) p)

#print axioms eq_second_permute_of_trivial_first
end MaxCaterpillar.Fiber.Count65.SectorQuotient
