import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraphQuadratic
import MaxCaterpillar.Frontier.StarCertificate.StarRelabel

/-! # Exact relabeling of unrestricted ordered Boolean quadratic matrices -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
open BigOperators

lemma booleanCoordinate_map (e : Equiv.Perm (Fin 5)) (i : Fin 5)
    (S : Finset (Fin 5)) :
    booleanCoordinate (e i) (S.map e.toEmbedding)=booleanCoordinate i S := by
  classical
  have h : e i∈S.map e.toEmbedding ↔ i∈S := by
    constructor
    · rintro hi
      obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hi
      have he : j=i := e.injective hji
      simpa only [he] using hj
    · intro hi
      exact Finset.mem_map.mpr ⟨i,hi,rfl⟩
  simp only [booleanCoordinate,h]

/-- Both sums are reindexed; no symmetry or cancellation convention is used. -/
theorem booleanQuadratic_map (a : ℝ) (b : Fin 5 → ℝ)
    (d : Fin 5 → Fin 5 → ℝ) (e : Equiv.Perm (Fin 5)) (S : Finset (Fin 5)) :
    booleanQuadratic a b d (S.map e.toEmbedding)=
      booleanQuadratic a (fun i => b (e i)) (fun i j => d (e i) (e j)) S := by
  have hlin : (∑ i, b i*booleanCoordinate i (S.map e.toEmbedding))=
      ∑ i,b (e i)*booleanCoordinate (e i) (S.map e.toEmbedding) :=
    (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  have hquad : (∑ i,∑ j,d i j*(booleanCoordinate i (S.map e.toEmbedding)*
      booleanCoordinate j (S.map e.toEmbedding)))=
      ∑ i,∑ j,d (e i) (e j)*(booleanCoordinate (e i) (S.map e.toEmbedding)*
        booleanCoordinate (e j) (S.map e.toEmbedding)) := by
    have houter : (∑ i,∑ j,d i j*(booleanCoordinate i (S.map e.toEmbedding)*
        booleanCoordinate j (S.map e.toEmbedding)))=
        ∑ i,∑ j,d (e i) j*(booleanCoordinate (e i) (S.map e.toEmbedding)*
          booleanCoordinate j (S.map e.toEmbedding)) :=
      (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    rw [houter]
    apply Finset.sum_congr rfl
    intro i _
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  unfold booleanQuadratic
  rw [hlin,hquad]
  simp_rw [booleanCoordinate_map]

/-- The direction agrees exactly with StarRelabel's inverse-reading convention. -/
theorem relabel_booleanQuadratic (a : ℝ) (b : Fin 5 → ℝ)
    (d : Fin 5 → Fin 5 → ℝ) (e : Equiv.Perm (Fin 5)) :
    relabelSetFunction (booleanQuadratic a b d) e.symm=
      booleanQuadratic a (fun i => b (e i)) (fun i j => d (e i) (e j)) := by
  funext S
  simpa only [relabelSetFunction,Equiv.symm_symm] using booleanQuadratic_map a b d e S

lemma relabel_empty (G : Finset (Fin 5) → ℝ) (e : Equiv.Perm (Fin 5)) :
    relabelSetFunction G e ∅=G ∅ := by simp [relabelSetFunction]

lemma relabel_full (G : Finset (Fin 5) → ℝ) (e : Equiv.Perm (Fin 5)) :
    relabelSetFunction G e Finset.univ=G Finset.univ := by
  have h : (Finset.univ : Finset (Fin 5)).map e.symm.toEmbedding=Finset.univ := by
    ext i
    simp only [Finset.mem_map,Finset.mem_univ,true_and]
    exact ⟨fun _ => trivial,fun _ => ⟨e i,e.symm_apply_apply i⟩⟩
  simp only [relabelSetFunction,h]

end MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
