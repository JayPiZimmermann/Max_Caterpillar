import MaxCaterpillar.Frontier.StarCertificate.StarLeafEquivarianceCore
import MaxCaterpillar.Frontier.StarCertificate.StarLeafNegation

/-! # Equivariance of the actual anchored ANOVA components

The transport theorem is generic for arbitrary finite leaf functions. Its
specialization consumes the already proved actual chamber-sum symmetry.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

section Generic
variable {L : Type*} [DecidableEq L] [Fintype L]

theorem leaf_map_sdiff (e : Equiv.Perm L) (S T : Finset L) :
    (S\T).map e.toEmbedding=S.map e.toEmbedding\T.map e.toEmbedding := by
  ext i
  simp only [Finset.mem_map_equiv,Finset.mem_sdiff]

theorem zeroOutside_leaf_permute (e : Equiv.Perm L) (T : Finset L) (z : L→ℝ) :
    zeroOutside T (fun i => z (e i))=
      fun i => zeroOutside (T.map e.toEmbedding) z (e i) := by
  funext i
  simp only [zeroOutside,Finset.mem_map_equiv,Equiv.symm_apply_apply]

theorem sum_powerset_leaf_map (e : Equiv.Perm L) (S : Finset L)
    (f : Finset L→ℝ) :
    (∑ T in S.powerset, f (T.map e.toEmbedding))=
      ∑ T in (S.map e.toEmbedding).powerset, f T := by
  apply Finset.sum_bij (fun T _ => T.map e.toEmbedding)
  · intro T hT
    exact Finset.mem_powerset.mpr
      (Finset.map_subset_map.mpr (Finset.mem_powerset.mp hT))
  · intro T _
    rfl
  · intro T U _ _ he
    exact e.finsetCongr.injective he
  · intro T hT
    refine ⟨T.map e.symm.toEmbedding,?_,?_⟩
    · apply Finset.mem_powerset.mpr
      have hh : T.map e.symm.toEmbedding ⊆
          (S.map e.toEmbedding).map e.symm.toEmbedding :=
        Finset.map_subset_map.mpr (Finset.mem_powerset.mp hT)
      simpa [Finset.map_map] using hh
    · simp [Finset.map_map]

theorem sum_compatible_leaf_map (e : Equiv.Perm L) (S A : Finset L)
    (f : Finset L→ℝ) :
    (∑ P in (Finset.univ : Finset L).powerset.filter (fun P => P∩S=A),
      f (P.map e.toEmbedding))=
      ∑ P in (Finset.univ : Finset L).powerset.filter
        (fun P => P∩S.map e.toEmbedding=A.map e.toEmbedding), f P := by
  apply Finset.sum_bij (fun P _ => P.map e.toEmbedding)
  · intro P hP
    apply Finset.mem_filter.mpr
    refine ⟨by simp,?_⟩
    rw [←Finset.map_inter,(Finset.mem_filter.mp hP).2]
  · intro P _
    rfl
  · intro P Q _ _ he
    exact e.finsetCongr.injective he
  · intro P hP
    refine ⟨P.map e.symm.toEmbedding,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨by simp,?_⟩
      have hh := congrArg (fun T : Finset L => T.map e.symm.toEmbedding)
        (Finset.mem_filter.mp hP).2
      simpa [Finset.map_inter,Finset.map_map] using hh
    · simp [Finset.map_map]

/-- Arbitrary finite subset-indexed leaf functions inherit component
equivariance from their genuine function-level equivariance. -/
theorem component_leaf_permute_of_equivariant
    (Ψ : Finset L→(L→ℝ)→ℝ) (e : Equiv.Perm L)
    (hΨ : ∀ P z, Ψ P (fun i => z (e i))=Ψ (P.map e.toEmbedding) z)
    (S A : Finset L) (z : L→ℝ) :
    component Ψ S A (fun i => z (e i))=
      component Ψ (S.map e.toEmbedding) (A.map e.toEmbedding) z := by
  unfold component
  conv_rhs =>
    rw [←sum_powerset_leaf_map e S (fun T =>
      (-1 : ℝ)^(S.map e.toEmbedding\T).card *
        ∑ P in (Finset.univ : Finset L).powerset.filter
          (fun P => P∩S.map e.toEmbedding=A.map e.toEmbedding), Ψ P (zeroOutside T z))]
  apply Finset.sum_congr rfl
  intro T _
  have hc : (S.map e.toEmbedding\T.map e.toEmbedding).card=(S\T).card := by
    rw [←leaf_map_sdiff,Finset.card_map]
  rw [hc]
  congr 1
  calc
    _ = ∑ P in (Finset.univ : Finset L).powerset.filter (fun P => P∩S=A),
        Ψ (P.map e.toEmbedding) (zeroOutside (T.map e.toEmbedding) z) := by
      apply Finset.sum_congr rfl
      intro P _
      rw [zeroOutside_leaf_permute,hΨ]
    _ = _ := sum_compatible_leaf_map e S A
      (fun P => Ψ P (zeroOutside (T.map e.toEmbedding) z))
end Generic

/-- Exact S4 transport for the actual real anchored expressions used by
the star certificate, with no coefficient or sign-cell hypothesis. -/
theorem component_starPsi_leaf_permute (e : Equiv.Perm (Fin 4))
    (S A : Finset (Fin 4)) (z : Fin 4→ℝ) :
    component starPsi S A (fun i => z (e i))=
      component starPsi (S.map e.toEmbedding) (A.map e.toEmbedding) z :=
  component_leaf_permute_of_equivariant starPsi e (starPsi_leaf_permute e) S A z

#print axioms component_leaf_permute_of_equivariant
#print axioms component_starPsi_leaf_permute
end MaxCaterpillar.Frontier.StarCertificate
