import research.sN.exponential_push_20261102.structural.FiniteIndex

set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.FiniteIndex.IndependentCheck
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
variable {N : ℕ} {J K : Type*} [Fintype J] [Fintype K]

example (A : J→Point N) (U : K→Point N) (W : K→J→ℝ)
    (L : Point N) (B : J→ℝ) (d : K→ℝ) (k : K) (x : Point N) :
    (indexedNetwork A U W L B d).inner (Fintype.equivFin K k) x=
      lin (U k) x+∑ j,W k j*relu (lin (A j) x) :=
  inner_indexed A U W L B d k x

example (A : J→Point N) (U : K→Point N) (W : K→J→ℝ)
    (L : Point N) (B : J→ℝ) (d : K→ℝ) (x : Point N) :
    (indexedNetwork A U W L B d).eval x=
      lin L x+(∑ j,B j*relu (lin (A j) x))+
        ∑ k,d k*relu (lin (U k) x+∑ j,W k j*relu (lin (A j) x)) :=
  eval_indexed A U W L B d x

example (A : J→Point N) (U : K→Point N) (W : K→J→ℝ)
    (L : Point N) (B : J→ℝ) (d : K→ℝ) (k : K) (a b : Fin N) :
    braidEdgeWeight (indexedNetwork A U W L B d).A
      ((indexedNetwork A U W L B d).W (Fintype.equivFin K k)) a b=
      -∑ j:J,if rowSupport (A j)={a,b} then W k j*|A j a| else 0 :=
  braidEdgeWeight_indexed A U W L B d k a b

/-- Empty first and second families are allowed, and the resulting actual
normalized network still computes the one-input maximum. -/
noncomputable def emptyModel : NormalizedNetwork 1 0 0 :=
  indexedNetwork (J:=PEmpty.{1}) (K:=PEmpty.{1})
    (fun j => PEmpty.elim j) (fun k => PEmpty.elim k)
    (fun k => PEmpty.elim k) (fun _ => 1)
    (fun j => PEmpty.elim j) (fun k => PEmpty.elim k)

example : emptyModel.TranslationNormalized := by
  apply (translationNormalized_indexed _ _ _ _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro j
    exact PEmpty.elim j
  · intro k
    exact PEmpty.elim k
  · norm_num [Fin.sum_univ_succ]

example (x : Point 1) : emptyModel.eval x=x 0 := by
  rw [emptyModel,eval_indexed]
  simp [lin,Fin.sum_univ_succ]

#print axioms MaxCaterpillar.ExponentialPush.FiniteIndex.inner_indexed
#print axioms MaxCaterpillar.ExponentialPush.FiniteIndex.eval_indexed
#print axioms MaxCaterpillar.ExponentialPush.FiniteIndex.rowSupport_indexed
#print axioms MaxCaterpillar.ExponentialPush.FiniteIndex.rowSupport_card_le_indexed
#print axioms MaxCaterpillar.ExponentialPush.FiniteIndex.translationNormalized_indexed
#print axioms MaxCaterpillar.ExponentialPush.FiniteIndex.braidEdgeWeight_indexed
end MaxCaterpillar.ExponentialPush.FiniteIndex.IndependentCheck
