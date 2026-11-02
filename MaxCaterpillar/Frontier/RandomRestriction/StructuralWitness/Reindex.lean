import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Localization

/-! Literal bijective input-coordinate reindexing of an indexed actual model.
Every original first and outer neuron index and coefficient is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
open BigOperators

variable {N m h₁ h₂ : ℕ}

noncomputable def reindexInputs (model : NormalizedNetwork N h₁ h₂) (e : Fin m ≃ Fin N) :
    NormalizedNetwork m h₁ h₂ where
  A j i := model.A j (e i)
  U k i := model.U k (e i)
  W := model.W
  L i := model.L (e i)
  B := model.B
  d := model.d

lemma lin_reindex (a : Point N) (e : Fin m ≃ Fin N) (x : Point m) :
    lin (fun i => a (e i)) x=lin a (fun i => x (e.symm i)) := by
  unfold lin
  exact Fintype.sum_equiv e _ _ (fun i => by
    change a (e i)*x i=a (e i)*x (e.symm (e i))
    rw [e.symm_apply_apply])

lemma inner_reindex (model : NormalizedNetwork N h₁ h₂) (e : Fin m ≃ Fin N)
    (k : Fin h₂) (x : Point m) :
    (reindexInputs model e).inner k x=model.inner k (fun i => x (e.symm i)) := by
  simp only [NormalizedNetwork.inner,reindexInputs,lin_reindex]

lemma eval_reindex (model : NormalizedNetwork N h₁ h₂) (e : Fin m ≃ Fin N) (x : Point m) :
    (reindexInputs model e).eval x=model.eval (fun i => x (e.symm i)) := by
  simp only [NormalizedNetwork.eval,NormalizedNetwork.inner,reindexInputs,lin_reindex]

lemma maximum_reindex [NeZero N] [NeZero m] (e : Fin m ≃ Fin N) (x : Point m) :
    Maximum N (fun i => x (e.symm i))=Maximum m x := by
  apply le_antisymm
  · apply (Maximum_le_iff _ _).mpr
    intro i
    exact le_Maximum x (e.symm i)
  · apply (Maximum_le_iff _ _).mpr
    intro i
    simpa only [e.symm_apply_apply] using
      le_Maximum (fun j => x (e.symm j)) (e i)

lemma reindexInputs_computes_max [NeZero N] [NeZero m]
    (model : NormalizedNetwork N h₁ h₂) (e : Fin m ≃ Fin N)
    (h : ∀ x,model.eval x=Maximum N x) :
    ∀ x,(reindexInputs model e).eval x=Maximum m x := by
  intro x
  rw [eval_reindex,h,maximum_reindex]

lemma sum_reindex (a : Point N) (e : Fin m ≃ Fin N) :
    (∑ i,a (e i))=∑ i,a i := Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma reindexInputs_translation_normalized (model : NormalizedNetwork N h₁ h₂)
    (e : Fin m ≃ Fin N) (h : model.TranslationNormalized) :
    (reindexInputs model e).TranslationNormalized := by
  refine ⟨?_,?_,?_⟩
  · intro j
    exact (sum_reindex (model.A j) e).trans (h.1 j)
  · intro k
    exact (sum_reindex (model.U k) e).trans (h.2.1 k)
  · exact (sum_reindex model.L e).trans h.2.2

lemma image_univ_equiv (e : Fin m ≃ Fin N) :
    Finset.univ.image e.toEmbedding=(Finset.univ : Finset (Fin N)) := by
  classical
  ext i
  constructor
  · intro _
    exact Finset.mem_univ i
  · intro _
    exact Finset.mem_image.mpr ⟨e.symm i,Finset.mem_univ _,e.apply_symm_apply i⟩

lemma card_rowSupport_reindex (a : Point N) (e : Fin m ≃ Fin N) :
    (NormalizedNetwork.rowSupport (fun i => a (e i))).card=
      (NormalizedNetwork.rowSupport a).card := by
  apply NormalizedNetwork.card_rowSupport_restrict e.toEmbedding a
  rw [image_univ_equiv]
  exact Finset.subset_univ _

#print axioms eval_reindex
#print axioms reindexInputs_computes_max
#print axioms reindexInputs_translation_normalized
#print axioms card_rowSupport_reindex
end MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
