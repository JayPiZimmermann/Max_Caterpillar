import MaxCaterpillar.Fiber.Count65.SectorQuotient.CanonicalRows
import MaxCaterpillar.Fiber.Count65.SectorQuotient.RootGraphs

/-! Complete first-frame rigidity under actual positive rescaling and finite
row/input permutations, including the star endpoint. -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

theorem mixed_frame_rigidity (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (s : Fin 6 → ℝ) (hs : ∀ j,0<s j)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (h : ∀ j i,Mixed65.firstRows t j i=s j*Mixed65.firstRows u (p j) (q i)) :
    t=u ∧ p=Equiv.refl _ ∧ q=Equiv.refl _ ∧ ∀ j,s j=1 := by
  have hq := mixed_input_perm_trivial t u ht hu p q s hs h
  subst q
  have hf := mixed_fixed_input_rigidity t u ht hu s hs p h
  exact ⟨hf.1,hf.2.1,rfl,hf.2.2⟩

theorem star_frame_rigidity (t u : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0<u) (hu1 : u≤1)
    (s : Fin 6 → ℝ) (hs : ∀ j,0<s j)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (h : ∀ j i,Star65.firstRows t j i=s j*Star65.firstRows u (p j) (q i)) :
    t=u ∧ p=Equiv.refl _ ∧ q=Equiv.refl _ ∧ ∀ j,s j=1 := by
  have hq := star_input_perm_trivial t u ht ht1 hu hu1 p q s hs h
  subst q
  have hf := star_fixed_input_rigidity t u ht hu s hs p h
  exact ⟨hf.1,hf.2.1,rfl,hf.2.2⟩

#print axioms mixed_frame_rigidity
#print axioms star_frame_rigidity
end MaxCaterpillar.Fiber.Count65.SectorQuotient
