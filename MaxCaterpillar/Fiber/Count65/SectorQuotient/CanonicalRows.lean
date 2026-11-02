import MaxCaterpillar.Fiber.Mixed65.Construction
import MaxCaterpillar.Fiber.Star65.Construction

/-! Actual positive-ray rigidity of the labeled canonical first matrices.
No network classification or orbit relation is built into these lemmas. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

private lemma vec4_three (a b c d : ℝ) :
    (![a,b,c,d] : Point 4) (3 : Fin 4)=d := rfl

lemma mixed_row_index_unique (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (j k : Fin 6) (s : ℝ) (hs : 0<s)
    (h : ∀ i,Mixed65.firstRows t j i=s*Mixed65.firstRows u k i) : j=k := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have hsu := mul_pos hs hu
  fin_cases j <;> fin_cases k <;> first | rfl |
    (exfalso
     simp only [Mixed65.firstRows,Matrix.cons_val_zero',Matrix.cons_val_succ',
       Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
       Matrix.head_cons,Matrix.tail_cons,vec4_three,mul_zero,mul_one,mul_neg,zero_mul,neg_zero]
       at h0 h1 h2 h3 <;>
       nlinarith only [ht,hu,hs,hsu,h0,h1,h2,h3])

lemma star_row_index_unique (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (j k : Fin 6) (s : ℝ) (hs : 0<s)
    (h : ∀ i,Star65.firstRows t j i=s*Star65.firstRows u k i) : j=k := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have hsu := mul_pos hs hu
  fin_cases j <;> fin_cases k <;> first | rfl |
    (exfalso
     simp only [Star65.firstRows,Matrix.cons_val_zero',Matrix.cons_val_succ',
       Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
       Matrix.head_cons,Matrix.tail_cons,vec4_three,mul_zero,mul_one,mul_neg,zero_mul,neg_zero]
       at h0 h1 h2 h3 <;>
       nlinarith only [ht,hu,hs,hsu,h0,h1,h2,h3])

/-- With the input labels fixed, no first-neuron permutation or positive
first-neuron scaling can identify distinct mixed canonical parameters. -/
theorem mixed_fixed_input_rigidity (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (s : Fin 6 → ℝ) (hs : ∀ j,0<s j) (p : Equiv.Perm (Fin 6))
    (h : ∀ j i,Mixed65.firstRows t j i=s j*Mixed65.firstRows u (p j) i) :
    t=u ∧ p=Equiv.refl _ ∧ ∀ j,s j=1 := by
  have hp : p=Equiv.refl _ := by
    apply Equiv.ext
    intro j
    exact (mixed_row_index_unique t u ht hu j (p j) (s j) (hs j) (h j)).symm
  subst p
  have hs1 : ∀ j,s j=1 := by
    intro j
    fin_cases j
    · change s (0 : Fin 6)=1
      have hh := h 0 0
      change 1=s 0*1 at hh
      linarith only [hh]
    · change s (1 : Fin 6)=1
      have hh := h 1 1
      change 1=s 1*1 at hh
      linarith only [hh]
    · change s (2 : Fin 6)=1
      have hh := h 2 3
      change 1=s 2*1 at hh
      linarith only [hh]
    · change s (3 : Fin 6)=1
      have hh := h 3 2
      change 1=s 3*1 at hh
      linarith only [hh]
    · change s (4 : Fin 6)=1
      have hh := h 4 2
      change 1=s 4*1 at hh
      linarith only [hh]
    · change s (5 : Fin 6)=1
      have hh := h 5 2
      change -1=s 5*(-1) at hh
      linarith only [hh]
  refine ⟨?_,rfl,hs1⟩
  have hh := h 3 0
  change t=s 3*u at hh
  simpa only [hs1 3,one_mul] using hh

/-- The same rigidity includes the star endpoint parameter one. -/
theorem star_fixed_input_rigidity (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (s : Fin 6 → ℝ) (hs : ∀ j,0<s j) (p : Equiv.Perm (Fin 6))
    (h : ∀ j i,Star65.firstRows t j i=s j*Star65.firstRows u (p j) i) :
    t=u ∧ p=Equiv.refl _ ∧ ∀ j,s j=1 := by
  have hp : p=Equiv.refl _ := by
    apply Equiv.ext
    intro j
    exact (star_row_index_unique t u ht hu j (p j) (s j) (hs j) (h j)).symm
  subst p
  have hs1 : ∀ j,s j=1 := by
    intro j
    fin_cases j
    · change s (0 : Fin 6)=1
      have hh := h 0 0
      change 1=s 0*1 at hh
      linarith only [hh]
    · change s (1 : Fin 6)=1
      have hh := h 1 1
      change 1=s 1*1 at hh
      linarith only [hh]
    · change s (2 : Fin 6)=1
      have hh := h 2 3
      change 1=s 2*1 at hh
      linarith only [hh]
    · change s (3 : Fin 6)=1
      have hh := h 3 0
      change 1=s 3*1 at hh
      linarith only [hh]
    · change s (4 : Fin 6)=1
      have hh := h 4 2
      change 1=s 4*1 at hh
      linarith only [hh]
    · change s (5 : Fin 6)=1
      have hh := h 5 2
      change -1=s 5*(-1) at hh
      linarith only [hh]
  refine ⟨?_,rfl,hs1⟩
  have hh := h 3 2
  change -t=s 3*(-u) at hh
  rw [hs1 3,one_mul] at hh
  linarith only [hh]

#print axioms mixed_fixed_input_rigidity
#print axioms star_fixed_input_rigidity
end MaxCaterpillar.Fiber.Count65.SectorQuotient
