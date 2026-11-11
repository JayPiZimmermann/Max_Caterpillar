import MaxCaterpillar.Frontier.RandomRestriction.ActualMatchingRank

/-! The three-row cancellation example is deliberately excluded by cleanliness.
The original fourth-supported row is retained; the two pair rows alone do not
determine the actual conditional rank. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ActualCleanSanityCheck
open BigOperators
open MaxCaterpillar MaxCaterpillar.Frontier MaxCaterpillar.Frontier.RandomRestriction
open DominantGap GoodEvent NormalizedNetwork Cartesian

@[simp] theorem valThree : ((3 : Fin 4) : ℕ) = 3 := rfl

noncomputable def r₁ : Point 4 := braidRoot 0 1
noncomputable def r₂ : Point 4 := braidRoot 2 3
noncomputable def cancellationNet : NormalizedNetwork 4 3 1 where
  A := fun j => if j = 0 then r₁ else if j = 1 then r₂ else r₁+r₂
  U := fun _ => 0
  W := fun _ j => if j = 2 then -1 else 1
  L := unitVec 0
  B := fun _ => 0
  d := fun _ => 0

def rho : Equiv.Perm (Fin 4) :=
  ((Equiv.swap 0 2).trans (Equiv.swap 0 3)).trans (Equiv.swap 0 1)

theorem cancellationNet_normalized : cancellationNet.TranslationNormalized := by
  refine ⟨?_,?_,?_⟩
  · intro j
    fin_cases j <;> simp only [Fin.sum_univ_succ] <;>
      norm_num [Fin.ext_iff,cancellationNet,r₁,r₂,braidRoot,unitVec]
  · intro k
    norm_num [cancellationNet]
  · simp only [Fin.sum_univ_succ]
    norm_num [Fin.ext_iff,cancellationNet,unitVec]

theorem cancellation_row_support : rowSupport (cancellationNet.A 2) = Finset.univ := by
  classical
  ext i
  fin_cases i <;> norm_num [Fin.ext_iff,Fin.lt_def,Fin.le_def,rowSupport,cancellationNet,r₁,r₂,braidRoot,unitVec]

theorem last_gap_is_selected_isolated : (3 : Fin 4) ∈ rankIsolatedGaps rho 2 := by
  rw [rankIsolatedGaps,mem_isolatedGaps]
  refine ⟨?_,by decide,?_⟩
  · rw [mem_smallRankGaps]
    norm_num [Fin.ext_iff,Fin.lt_def,Fin.le_def,rho,Equiv.swap_apply_def]
  · intro h hh
    rw [mem_smallRankGaps] at hh
    fin_cases h <;> norm_num [Fin.ext_iff,Fin.lt_def,Fin.le_def,rho,Equiv.swap_apply_def] at hh ⊢

theorem cancellation_row_dominant :
    GapDominant (Equiv.refl (Fin 4),rho)
      (collapsedRow (Function.Embedding.refl (Fin 4)) (cancellationNet.A 2)) 3 := by
  have hc : ∀ g : Fin 4,
      tailCoefficient (Equiv.refl (Fin 4),rho)
        (collapsedRow (Function.Embedding.refl (Fin 4)) (cancellationNet.A 2)) g =
          if g = 1 ∨ g = 3 then 1 else 0 := by
    intro g
    fin_cases g <;> simp only [tailCoefficient,Finset.sum_filter,Fin.sum_univ_succ] <;>
      norm_num [Fin.ext_iff,Fin.lt_def,Fin.le_def,collapsedRow,cancellationNet,r₁,r₂,braidRoot,unitVec]
  refine ⟨?_,?_⟩
  · rw [hc]
    norm_num
  · intro g hg hne
    rw [hc] at hg
    fin_cases g <;> norm_num [Fin.ext_iff,Fin.lt_def,Fin.le_def,rho,Equiv.swap_apply_def] at hg hne ⊢

/-- The concrete rows r1,r2,r1+r2 with weights 1,1,-1 do not satisfy the
cleanliness prerequisite of the actual matching-rank theorem. -/
theorem cancellation_example_not_clean :
    ¬ActualClean cancellationNet (Function.Embedding.refl (Fin 4)) 0 rho 2 (Equiv.refl _) := by
  intro h
  apply h 2 (by norm_num [Fin.ext_iff,Fin.lt_def,Fin.le_def,cancellationNet])
    (by rw [cancellation_row_support]; norm_num) 3 last_gap_is_selected_isolated
  exact cancellation_row_dominant

#print axioms cancellationNet_normalized
#print axioms cancellation_row_support
#print axioms last_gap_is_selected_isolated
#print axioms cancellation_row_dominant
#print axioms cancellation_example_not_clean
end ActualCleanSanityCheck
