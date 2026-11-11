import MaxCaterpillar.Frontier.RandomRestriction.BraidCoinColumn
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Support

/-! # Exact signed edge weights under literal masked coordinate restriction

Original row indices remain unchanged. The statements permit arbitrary
ambient support size and arbitrary signed, parallel and cancelling rows.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Frontier.RandomRestriction.BraidModel
open BigOperators NormalizedNetwork
variable {N m h₁ : ℕ}

theorem pair_support_inside_embedding (e : Fin m ↪ Fin N)
    (A : Point N) (a b : Fin m) (h : rowSupport A={e a,e b}) :
    rowSupport A⊆Finset.univ.image e := by
  classical
  rw [h]
  intro i hi
  rcases Finset.mem_insert.mp hi with hi | hi
  · subst i
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  · have he : i=e b := Finset.mem_singleton.mp hi
    subst i
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩

theorem masked_restrict_pair_support_iff (e : Fin m ↪ Fin N)
    (A : Point N) (Q : Point m)
    (hQ : Q=if rowSupport A⊆Finset.univ.image e then restrict e A else 0)
    (a b : Fin m) :
    rowSupport Q={a,b} ↔ rowSupport A={e a,e b} := by
  classical
  constructor
  · intro hpair
    by_cases hkeep : rowSupport A⊆Finset.univ.image e
    · have himage : (rowSupport Q).image e=rowSupport A := by
        rw [hQ,if_pos hkeep]
        exact image_rowSupport_restrict_of_subset e A hkeep
      rw [hpair] at himage
      simpa using himage.symm
    · rw [hQ,if_neg hkeep,rowSupport_zero] at hpair
      have ha : a∈({a,b} : Finset (Fin m)) := by simp
      rw [←hpair] at ha
      exact False.elim (Finset.not_mem_empty a ha)
  · intro hpair
    have hkeep := pair_support_inside_embedding e A a b hpair
    apply Finset.image_injective e.injective
    rw [hQ,if_pos hkeep,image_rowSupport_restrict_of_subset e A hkeep,hpair]
    simp

/-- The exact-support row filter is preserved, not merely included. -/
theorem braidEdgeRows_masked_restrict (e : Fin m ↪ Fin N)
    (A : Fin h₁→Point N) (Q : Fin h₁→Point m)
    (hQ : ∀ j, Q j=if rowSupport (A j)⊆Finset.univ.image e then restrict e (A j) else 0)
    (a b : Fin m) : braidEdgeRows Q a b=braidEdgeRows A (e a) (e b) := by
  classical
  ext j
  simp only [braidEdgeRows,Finset.mem_filter,Finset.mem_univ,true_and]
  exact masked_restrict_pair_support_iff e (A j) (Q j) (hQ j) a b

/-- Literal masked restriction preserves each full signed aggregate edge
weight. Equality includes all cancellations among original parallel rows.
Weights on discarded rows are unrestricted, since those rows are zero. -/
theorem braidEdgeWeight_masked_restrict (e : Fin m ↪ Fin N)
    (A : Fin h₁→Point N) (W : Fin h₁→ℝ)
    (Q : Fin h₁→Point m) (V : Fin h₁→ℝ)
    (hQ : ∀ j, Q j=if rowSupport (A j)⊆Finset.univ.image e then restrict e (A j) else 0)
    (hV : ∀ j, rowSupport (A j)⊆Finset.univ.image e → V j=W j)
    (a b : Fin m) :
    braidEdgeWeight Q V a b=braidEdgeWeight A W (e a) (e b) := by
  classical
  unfold braidEdgeWeight
  rw [braidEdgeRows_masked_restrict e A Q hQ a b]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hp : rowSupport (A j)={e a,e b} := (Finset.mem_filter.mp hj).2
  have hkeep := pair_support_inside_embedding e (A j) a b hp
  have hvalue : Q j a=A j (e a) := by
    rw [hQ j,if_pos hkeep]
    rfl
  rw [hV j hkeep,hvalue]

#print axioms masked_restrict_pair_support_iff
#print axioms braidEdgeRows_masked_restrict
#print axioms braidEdgeWeight_masked_restrict
end MaxCaterpillar.Frontier.RandomRestriction.BraidModel
