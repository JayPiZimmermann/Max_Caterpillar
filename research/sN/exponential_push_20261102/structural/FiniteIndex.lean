import MaxCaterpillar.Frontier.RandomRestriction.BraidCoinColumn
import Mathlib.Tactic

/-! Reindex arbitrary finite first/second families as actual indexed networks.
No nonempty-index assumptions are required. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.FiniteIndex
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork
variable {N : ℕ} {J K : Type*} [Fintype J] [Fintype K]

/-- A finite family can be reindexed without altering any summand. -/
theorem sum_equivFin_symm (f : J→ℝ) :
    (∑ i : Fin (Fintype.card J), f ((Fintype.equivFin J).symm i))=∑ j,f j := by
  exact Equiv.sum_comp (Fintype.equivFin J).symm f

noncomputable def indexedNetwork (A : J→Point N) (U : K→Point N)
    (W : K→J→ℝ) (L : Point N) (B : J→ℝ) (d : K→ℝ) :
    NormalizedNetwork N (Fintype.card J) (Fintype.card K) where
  A := fun j => A ((Fintype.equivFin J).symm j)
  U := fun k => U ((Fintype.equivFin K).symm k)
  W := fun k j => W ((Fintype.equivFin K).symm k) ((Fintype.equivFin J).symm j)
  L := L
  B := fun j => B ((Fintype.equivFin J).symm j)
  d := fun k => d ((Fintype.equivFin K).symm k)

@[simp] theorem rowSupport_indexed (A : J→Point N) (U : K→Point N)
    (W : K→J→ℝ) (L : Point N) (B : J→ℝ) (d : K→ℝ) (j : J) :
    rowSupport ((indexedNetwork A U W L B d).A (Fintype.equivFin J j))=
      rowSupport (A j) := by
  simp only [indexedNetwork,Equiv.symm_apply_apply]

/-- The actual unrectified outer value at the original finite outer index. -/
theorem inner_indexed (A : J→Point N) (U : K→Point N)
    (W : K→J→ℝ) (L : Point N) (B : J→ℝ) (d : K→ℝ)
    (k : K) (x : Point N) :
    (indexedNetwork A U W L B d).inner (Fintype.equivFin K k) x=
      lin (U k) x+∑ j,W k j*relu (lin (A j) x) := by
  simp only [NormalizedNetwork.inner,indexedNetwork,Equiv.symm_apply_apply]
  rw [sum_equivFin_symm (fun j => W k j*relu (lin (A j) x))]

/-- The complete real network identity, with all arbitrary skips retained. -/
theorem eval_indexed (A : J→Point N) (U : K→Point N)
    (W : K→J→ℝ) (L : Point N) (B : J→ℝ) (d : K→ℝ) (x : Point N) :
    (indexedNetwork A U W L B d).eval x=
      lin L x+(∑ j,B j*relu (lin (A j) x))+
      ∑ k,d k*relu (lin (U k) x+∑ j,W k j*relu (lin (A j) x)) := by
  unfold NormalizedNetwork.eval
  have hi (i : Fin (Fintype.card K)) :
      (indexedNetwork A U W L B d).inner i x=
        lin (U ((Fintype.equivFin K).symm i)) x+
          ∑ j,W ((Fintype.equivFin K).symm i) j*relu (lin (A j) x) := by
    simpa only [Equiv.apply_symm_apply] using
      inner_indexed A U W L B d ((Fintype.equivFin K).symm i) x
  simp_rw [hi]
  change lin L x+
    (∑ i : Fin (Fintype.card J),B ((Fintype.equivFin J).symm i)*
      relu (lin (A ((Fintype.equivFin J).symm i)) x))+
    (∑ i : Fin (Fintype.card K),d ((Fintype.equivFin K).symm i)*
      relu (lin (U ((Fintype.equivFin K).symm i)) x+
        ∑ j,W ((Fintype.equivFin K).symm i) j*relu (lin (A j) x)))=_
  rw [sum_equivFin_symm (fun j => B j*relu (lin (A j) x)),
    sum_equivFin_symm (fun k => d k*relu (lin (U k) x+∑ j,W k j*relu (lin (A j) x)))]

/-- Translation normalization is exactly the original finite-family condition. -/
theorem translationNormalized_indexed (A : J→Point N) (U : K→Point N)
    (W : K→J→ℝ) (L : Point N) (B : J→ℝ) (d : K→ℝ) :
    (indexedNetwork A U W L B d).TranslationNormalized ↔
      (∀ j,∑ i,A j i=0) ∧ (∀ k,∑ i,U k i=0) ∧ ∑ i,L i=1 := by
  constructor
  · rintro ⟨ha,hu,hl⟩
    refine ⟨?_,?_,hl⟩
    · intro j
      simpa only [indexedNetwork,Equiv.symm_apply_apply] using ha (Fintype.equivFin J j)
    · intro k
      simpa only [indexedNetwork,Equiv.symm_apply_apply] using hu (Fintype.equivFin K k)
  · rintro ⟨ha,hu,hl⟩
    exact ⟨fun i => ha ((Fintype.equivFin J).symm i),
      fun k => hu ((Fintype.equivFin K).symm k),hl⟩

/-- Reindexing retains the exact signed parallel-row sum, with no positivity
or no-cancellation hypothesis and no nonempty family hypothesis. -/
theorem braidEdgeWeight_indexed (A : J→Point N) (U : K→Point N)
    (W : K→J→ℝ) (L : Point N) (B : J→ℝ) (d : K→ℝ)
    (k : K) (a b : Fin N) :
    braidEdgeWeight (indexedNetwork A U W L B d).A
      ((indexedNetwork A U W L B d).W (Fintype.equivFin K k)) a b=
      -∑ j : J, if rowSupport (A j)={a,b} then W k j*|A j a| else 0 := by
  classical
  simp only [braidEdgeWeight,braidEdgeRows,Finset.sum_filter,indexedNetwork,
    Equiv.symm_apply_apply]
  rw [Finset.sum_filter]
  rw [sum_equivFin_symm (fun j =>
    if rowSupport (A j)={a,b} then W k j*|A j a| else 0)]

/-- The first-row support bound is exactly invariant under reindexing. -/
theorem rowSupport_card_le_indexed (A : J→Point N) (U : K→Point N)
    (W : K→J→ℝ) (L : Point N) (B : J→ℝ) (d : K→ℝ) (r : ℕ) :
    (∀ i,(rowSupport ((indexedNetwork A U W L B d).A i)).card≤r) ↔
      ∀ j,(rowSupport (A j)).card≤r := by
  constructor
  · intro h j
    simpa only [indexedNetwork,Equiv.symm_apply_apply] using h (Fintype.equivFin J j)
  · intro h i
    exact h ((Fintype.equivFin J).symm i)


#print axioms sum_equivFin_symm
#print axioms inner_indexed
#print axioms eval_indexed
#print axioms translationNormalized_indexed
#print axioms braidEdgeWeight_indexed
end MaxCaterpillar.ExponentialPush.FiniteIndex
