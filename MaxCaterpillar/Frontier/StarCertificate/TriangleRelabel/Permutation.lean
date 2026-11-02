import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraph
import MaxCaterpillar.Frontier.RandomRestriction.UniformTuples

/-! # Every triangle-supported graph admits a genuine three-coordinate relabeling

The three vertices in TriangleContained may coincide. Their finite cover is
first padded to three distinct vertices inside Fin5, then its enumeration is
extended to a permutation of the entire actual ground set.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
open RandomRestriction.UniformTuples

/-- No distinctness assumption on the original three covering vertices. -/
theorem triangleContained_permutation (G : SimpleGraph (Fin 5))
    (h : TriangleContained G) :
    ∃ e : Equiv.Perm (Fin 5), ∀ i j, G.Adj (e i) (e j) → i.val<3 ∧ j.val<3 := by
  classical
  obtain ⟨a,b,c,hcover⟩ := h
  let S : Finset (Fin 5) := {a,b,c}
  have hsmall : S.card≤3 := by
    have h1 := Finset.card_insert_le a ({b,c} : Finset (Fin 5))
    have h2 := Finset.card_insert_le b ({c} : Finset (Fin 5))
    simp only [Finset.card_singleton] at h2
    change ({a,b,c} : Finset (Fin 5)).card≤3
    linarith only [h1,h2]
  have hbound : (3-S.card)+S.card≤(Finset.univ : Finset (Fin 5)).card := by
    rw [Nat.sub_add_cancel hsmall,Finset.card_univ,Fintype.card_fin]
    decide
  obtain ⟨T,hST,_,hT⟩ := Finset.exists_intermediate_set (3-S.card) hbound
    (Finset.subset_univ S)
  rw [Nat.sub_add_cancel hsmall] at hT
  let order : Fin 3 ≃ T :=
    (Fintype.equivFinOfCardEq (show Fintype.card T=3 by rw [Fintype.card_coe,hT])).symm
  let emb : Fin 3 ↪ Fin 5 := order.toEmbedding.trans
    (Function.Embedding.subtype fun i => i∈T)
  obtain ⟨e,he⟩ := exists_permutation_between
    ((Fin.castAddEmb 2).toEmbedding : Fin 3 ↪ Fin 5) emb
  have hprefix : ∀ i : Fin 5, e i∈T → i.val<3 := by
    intro i hi
    let k : Fin 3 := order.symm ⟨e i,hi⟩
    have hk : emb k=e i := by
      change (order k).val=e i
      exact congrArg Subtype.val (order.apply_symm_apply ⟨e i,hi⟩)
    have hiEq : Fin.castAdd 2 k=i := e.injective ((he k).trans hk)
    rw [← hiEq]
    exact k.isLt
  refine ⟨e,?_⟩
  intro i j hij
  have hc := hcover (e i) (e j) hij
  have hi : e i∈S := by simpa [S] using hc.1
  have hj : e j∈S := by simpa [S] using hc.2
  exact ⟨hprefix i (hST hi),hprefix j (hST hj)⟩

end MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
