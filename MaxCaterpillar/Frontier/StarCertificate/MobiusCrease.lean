import MaxCaterpillar.Frontier.StarCertificate.CreasePositive

/-! # Finite projective grouping of actual chamber creases

The cancellation premise is an equality of functions on the positive gap
cone. Even homogeneous functionals vanish after grouping complete real
lines; no cancellation conclusion is assumed in the theorem statement.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def HasMixedCoordinates {n : ℕ} (w : Point n) : Prop :=
  (∃ a, w a<0) ∧ (∃ a, 0<w a)

theorem even_homogeneous_mul {n : ℕ} (f : Point n→ℝ)
    (heven : ∀ w, f (-w)=f w)
    (hhom : ∀ c : ℝ, 0<c → ∀ w, f (c•w)=c*f w)
    (hzero : f 0=0) (c : ℝ) (w : Point n) :
    f (c•w)=|c| *f w := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have he : c•w=(-c)•(-w) := by ext i; simp
    rw [he,hhom (-c) (neg_pos.mpr hc),heven,abs_of_neg hc]
  · subst c
    simp [hzero]
  · rw [hhom c hc,abs_of_pos hc]

/-- Two indices have the same unoriented nonzero-scalar line. Zero vectors
form a separate class, so these really are disjoint finite classes. -/
def coefficientLineSetoid {n : ℕ} {ι : Type*} (w : ι→Point n) : Setoid ι where
  r i j := ∃ a : ℝ, a≠0 ∧ w i=a•w j
  iseqv := by
    refine ⟨?_,?_,?_⟩
    · intro i
      exact ⟨1,one_ne_zero,by simp⟩
    · intro i j h
      obtain ⟨a,ha,he⟩ := h
      refine ⟨a⁻¹,inv_ne_zero ha,?_⟩
      rw [he,smul_smul,inv_mul_cancel ha,one_smul]
    · intro i j k hij hjk
      obtain ⟨a,ha,he⟩ := hij
      obtain ⟨b,hb,hf⟩ := hjk
      exact ⟨a*b,mul_ne_zero ha hb,by rw [he,hf,smul_smul]⟩

/-- Every actual finite affine ReLU identity on the positive cone cancels
every even positively homogeneous functional supported on mixed vectors.
The proof includes zero forms in each analytic parallel group; their
functional contributions vanish before the disjoint quotient summation. -/
theorem positive_gap_even_functional_cancel {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι→Point n) (c : ι→ℝ) (l : Point n) (β : ℝ)
    (h : ∀ x : Point n, (∀ j, 0<x j) →
      lin l x+β=∑ i, c i*relu (lin (w i) x))
    (f : Point n→ℝ)
    (heven : ∀ v, f (-v)=f v)
    (hhom : ∀ a : ℝ, 0<a → ∀ v, f (a•v)=a*f v)
    (hzero : f 0=0)
    (hnonmixed : ∀ v, ¬ HasMixedCoordinates v → f v=0) :
    (∑ i, c i*f (w i))=0 := by
  classical
  let S := coefficientLineSetoid w
  let key : ι→Quotient S := Quotient.mk''
  have habs := even_homogeneous_mul f heven hhom hzero
  have hfiber : ∀ q : Quotient S,
      (∑ i in Finset.univ.filter (fun i => key i=q), c i*f (w i))=0 := by
    intro q
    let t : ι := Quotient.out q
    have hrep : key t=q := Quotient.out_eq q
    have hrelated : ∀ i, key i=q → ∃ a : ℝ, a≠0 ∧ w i=a•w t := by
      intro i hi
      exact Quotient.exact (hi.trans hrep.symm)
    by_cases hm : HasMixedCoordinates (w t)
    · let J := Finset.univ.filter (fun i => ∃ a : ℝ, w i=a•w t)
      have hex : ∀ i∈J, ∃ a : ℝ, w i=a•w t := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      let scale : ι→ℝ := fun i => if hi : i∈J then Classical.choose (hex i hi) else 0
      have hparallel : ∀ i∈J, w i=scale i•w t := by
        intro i hi
        simpa only [scale,dif_pos hi] using Classical.choose_spec (hex i hi)
      have hnonparallel : ∀ i∉J, ¬∃ a : ℝ, w i=a•w t := by
        intro i hi he
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
      have hmass := positive_gap_parallel_crease_cancel w c l β h (w t)
        hm.1 hm.2 J scale hparallel hnonparallel
      have hJ : (∑ i in J, c i*f (w i))=0 := by
        calc
          _ = (∑ i in J, c i*|scale i|)*f (w t) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hparallel i hi,habs]
            ring
          _ = 0 := by rw [hmass,zero_mul]
      have hsub : Finset.univ.filter (fun i => key i=q) ⊆ J := by
        intro i hi
        obtain ⟨a,_,he⟩ := hrelated i (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,he⟩
      have heq : (∑ i in Finset.univ.filter (fun i => key i=q), c i*f (w i)) =
          ∑ i in J, c i*f (w i) := by
        apply Finset.sum_subset hsub
        intro i hi hout
        obtain ⟨a,he⟩ := hex i hi
        have ha : a=0 := by
          by_contra hne
          apply hout
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _,?_⟩
          have hsame : key i=key t := Quotient.sound (show S.r i t from ⟨a,hne,he⟩)
          exact hsame.trans hrep
        rw [ha,zero_smul] at he
        rw [he,hzero,mul_zero]
      exact heq.trans hJ
    · apply Finset.sum_eq_zero
      intro i hi
      obtain ⟨a,_,he⟩ := hrelated i (Finset.mem_filter.mp hi).2
      rw [he,habs,hnonmixed (w t) hm,mul_zero,mul_zero]
  calc
    _ = ∑ q : Quotient S, ∑ i in Finset.univ.filter (fun i => key i=q),
        c i*f (w i) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (key i)) _
    _ = 0 := Finset.sum_eq_zero (fun q _ => hfiber q)

#print axioms positive_gap_even_functional_cancel
end MaxCaterpillar.Frontier.StarCertificate
