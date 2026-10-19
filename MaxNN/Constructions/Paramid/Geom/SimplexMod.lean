import MaxNN.Constructions.Paramid.Geom.Complete
import MaxNN.Constructions.Paramid.Geom.Coordinates
import MaxNN.Constructions.Paramid.Geom.Kuhn

/-! # Full-dimensional simplex support functions modulo lower dimension -/

namespace MaxNN.ParamidGeom.KuhnRhoAux

open BigOperators

noncomputable section

def simplexFns (m : ℕ) : Set ((Fin m → ℝ) → ℝ) :=
  {f | ∃ P : Fin (m + 1) → Fin m → ℝ, AffineIndependent ℝ P ∧ f = hS (Finset.univ.image P)}

def simplexMod (m : ℕ) : Submodule ℝ ((Fin m → ℝ) → ℝ) :=
  Submodule.span ℝ (simplexFns m) ⊔ LSpan m (m - 1)

theorem simplexMod_le_SSpan (m : ℕ) : simplexMod m ≤ SSpan m := by
  refine sup_le ?_ (LSpan_le_SSpan m (m - 1))
  rw [Submodule.span_le]
  rintro f ⟨P, -, rfl⟩
  exact GermAux.hS_mem_SSpan (Finset.univ_nonempty.image P)

theorem exists_sum_of_mem_span_simplexFns {m : ℕ} {g : (Fin m → ℝ) → ℝ}
    (hg : g ∈ Submodule.span ℝ (simplexFns m)) :
    ∃ (r : ℕ) (a : Fin r → ℝ) (P : Fin r → Fin (m + 1) → Fin m → ℝ),
      (∀ i, AffineIndependent ℝ (P i)) ∧
        g = fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y := by
  obtain ⟨r, a, G, hG⟩ := mem_span_set'.mp hg
  have hGP : ∀ i, ∃ P : Fin (m + 1) → Fin m → ℝ, AffineIndependent ℝ P ∧
      (G i : (Fin m → ℝ) → ℝ) = hS (Finset.univ.image P) := fun i => (G i).2
  choose P hP hPe using hGP
  refine ⟨r, a, P, hP, ?_⟩
  rw [← hG]
  funext y
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, hPe i]

def stdVerts (n : ℕ) : Fin (n + 1) → Fin n → ℝ :=
  Fin.cons 0 (fun i => (Pi.single i 1 : Fin n → ℝ))

theorem stdVerts_zero (n : ℕ) : stdVerts n 0 = 0 := Fin.cons_zero _ _

theorem stdVerts_succ (n : ℕ) (i : Fin n) : stdVerts n i.succ = Pi.single i 1 :=
  Fin.cons_succ _ _ _

theorem univ_image_stdVerts (n : ℕ) : Finset.univ.image (stdVerts n) = simplexVerts n := by
  ext p
  unfold simplexVerts
  rw [Finset.mem_image, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨i, -, rfl⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact Or.inl (stdVerts_zero n)
    · exact Or.inr ⟨j, Finset.mem_univ j, (stdVerts_succ n j).symm⟩
  · rintro (rfl | ⟨j, -, rfl⟩)
    · exact ⟨0, Finset.mem_univ _, stdVerts_zero n⟩
    · exact ⟨j.succ, Finset.mem_univ _, stdVerts_succ n j⟩

theorem stdVerts_affineIndependent (n : ℕ) : AffineIndependent ℝ (stdVerts n) := by
  unfold stdVerts
  apply Kuhn.affineIndependent_cons_zero
  have e : (fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)) = ⇑(Pi.basisFun ℝ (Fin n)) := by
    funext i
    rw [Pi.basisFun_apply]
    rfl
  rw [e]
  exact (Pi.basisFun ℝ (Fin n)).linearIndependent

theorem hS_simplexVerts_mem_simplexMod (n : ℕ) : hS (simplexVerts n) ∈ simplexMod n := by
  refine Submodule.mem_sup_left
    (Submodule.subset_span ⟨stdVerts n, stdVerts_affineIndependent n, ?_⟩)
  rw [univ_image_stdVerts]

/-- The support function of the standard triangle. -/
theorem hS_simplexVerts_two (y : Fin 2 → ℝ) :
    hS (simplexVerts 2) y = max 0 (max (y 0) (y 1)) := by
  have h0 : (0 : Fin 2 → ℝ) ∈ simplexVerts 2 := Finset.mem_insert_self _ _
  have hi : ∀ i : Fin 2, (Pi.single i 1 : Fin 2 → ℝ) ∈ simplexVerts 2 := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hy : ∀ i : Fin 2, y i ≤ max (y 0) (y 1) :=
    Fin.forall_fin_two.mpr ⟨le_max_left _ _, le_max_right _ _⟩
  rw [hS_of_nonempty ⟨0, h0⟩]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun p hp => ?_
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rw [CoordAux.dot_zero_left]
      exact le_max_left _ _
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      rw [CompleteAux.dot_single_left]
      exact le_trans (hy i) (le_max_right _ _)
  · refine max_le ?_ ?_
    · have h := GermAux.dot_le_hS h0 y
      rw [hS_of_nonempty ⟨0, h0⟩, CoordAux.dot_zero_left] at h
      exact h
    · exact max_le
        (by
          have h := GermAux.dot_le_hS (hi 0) y
          rw [hS_of_nonempty ⟨0, h0⟩, CompleteAux.dot_single_left] at h
          exact h)
        (by
          have h := GermAux.dot_le_hS (hi 1) y
          rw [hS_of_nonempty ⟨0, h0⟩, CompleteAux.dot_single_left] at h
          exact h)

theorem paramidUnit_mem_simplexMod {m k : ℕ} {γ : Fin m → ℝ} {v : Fin k → Fin m → ℝ}
    (h : LinearIndependent ℝ (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ)) (hm : k + 1 = m) :
    MaxNN.paramidUnit γ v ∈ simplexMod m := by
  subst hm
  have h1 := paramidUnit_sub_kuhn_mem_LSpan h rfl
  have h2 : (∑ σ : Equiv.Perm (Fin k), hS (Finset.univ.image (kuhnVerts γ v σ))) ∈
      Submodule.span ℝ (simplexFns (k + 1)) :=
    Submodule.sum_mem _ fun σ _ =>
      Submodule.subset_span ⟨kuhnVerts γ v σ, kuhnVerts_affineIndependent h σ, rfl⟩
  have e : MaxNN.paramidUnit γ v = (fun y => MaxNN.paramidUnit γ v y -
      ∑ σ : Equiv.Perm (Fin k), hS (Finset.univ.image (kuhnVerts γ v σ)) y) +
      ∑ σ : Equiv.Perm (Fin k), hS (Finset.univ.image (kuhnVerts γ v σ)) := by
    funext y
    simp only [Pi.add_apply, Finset.sum_apply, sub_add_cancel]
  rw [e]
  exact Submodule.add_mem _ (Submodule.mem_sup_right h1) (Submodule.mem_sup_left h2)

end

end MaxNN.ParamidGeom.KuhnRhoAux
