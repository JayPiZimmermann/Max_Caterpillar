import MaxCaterpillar.Frontier.StarCertificate.StarPermutations

/-! # Relabeling invariance of the all-permutations chain sum

The chain functional is arbitrary. No evenness, homogeneity, or certificate
hypothesis is needed for the relabeling identity itself.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- Relabel the ground set by `e`, using its inverse to read the old function. -/
noncomputable def relabelSetFunction (G : Finset (Fin 5) → ℝ)
    (e : Equiv.Perm (Fin 5)) (B : Finset (Fin 5)) : ℝ :=
  G (B.map e.symm.toEmbedding)

/-- Relabeling a prefix composes its ordering with the same inverse map. -/
theorem permutationPrefix_map (e pi : Equiv.Perm (Fin 5)) (r : Fin 4) :
    (permutationPrefix pi r).map e.symm.toEmbedding =
      permutationPrefix (e.symm * pi) r := by
  ext i
  simp only [Finset.mem_map,permutationPrefix,Finset.mem_filter,
    Finset.mem_univ,true_and]
  change (∃ j,(∃ k : Fin 5,k.val≤r.val ∧ pi k=j) ∧ e.symm j=i) ↔
    ∃ k : Fin 5,k.val≤r.val ∧ e.symm (pi k)=i
  constructor
  · rintro ⟨j,⟨k,hkr,hkj⟩,hji⟩
    exact ⟨k,hkr,by rw [hkj]; exact hji⟩
  · rintro ⟨k,hkr,hki⟩
    exact ⟨pi k,⟨k,hkr,rfl⟩,hki⟩

theorem permutationFunctionChain_relabel (G : Finset (Fin 5) → ℝ)
    (e pi : Equiv.Perm (Fin 5)) :
    permutationFunctionChain (relabelSetFunction G e) pi =
      permutationFunctionChain G (e.symm * pi) := by
  funext r
  change G ((permutationPrefix pi r).map e.symm.toEmbedding) =
    G (permutationPrefix (e.symm * pi) r)
  rw [permutationPrefix_map]

/-- An arbitrary functional of the four chain coordinates has the same
sum over all orderings after any relabeling of the ground set. -/
theorem permutation_relabel_sum {R : Type*} [AddCommMonoid R]
    (G : Finset (Fin 5) → ℝ) (e : Equiv.Perm (Fin 5))
    (Xi : (Fin 4 → ℝ) → R) :
    (∑ pi : Equiv.Perm (Fin 5),Xi (permutationFunctionChain (relabelSetFunction G e) pi)) =
      ∑ pi : Equiv.Perm (Fin 5),Xi (permutationFunctionChain G pi) := by
  simp_rw [permutationFunctionChain_relabel]
  exact Fintype.sum_equiv (Equiv.mulLeft e.symm) _ _ (fun _ => rfl)

/-- The coefficient certificate, once attached, applies to every relabeling
of the actual centre-4 real-slope star set function. -/
theorem star_permutation_relabel_sum_of_coefficients
    (hcoeff : ∀ (z : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z=0)
    (v v' : Fin 4 → ℝ) (e : Equiv.Perm (Fin 5)) :
    (∑ pi : Equiv.Perm (Fin 5),starXi
      (permutationFunctionChain (relabelSetFunction (starSetFunction v v') e) pi))=0 := by
  rw [permutation_relabel_sum]
  exact star_permutation_sum_of_coefficients hcoeff v v'

#print axioms permutationPrefix_map
#print axioms permutation_relabel_sum
#print axioms star_permutation_relabel_sum_of_coefficients
end MaxCaterpillar.Frontier.StarCertificate
