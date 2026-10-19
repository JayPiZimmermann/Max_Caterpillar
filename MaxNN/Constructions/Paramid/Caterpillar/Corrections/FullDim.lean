import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Formula
import MaxNN.Constructions.Paramid.Geom.SimplexMod

/-!
# Full dimensionality of every caterpillar word cone

The tree edges span every difference from the first base vertex.  Adding the
apex-to-last-head vector therefore spans all differences from the apex to the
other simplex vertices.  Those differences are linearly independent.
-/

namespace MaxNN.Caterpillar.Corrections

open BigOperators ParamidGeom MaxNN.Width MaxNN.ParamidChain

variable {m r : ℕ}

private theorem add_sum_mem_coneVertsOn (γ : Fin m → ℝ) {V I : Finset (Fin m → ℝ)}
    (hI : I ⊆ V) : γ + ∑ v in I, v ∈ coneVertsOn γ V :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr hI))

private theorem zero_mem_coneVertsOn (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    (0 : Fin m → ℝ) ∈ coneVertsOn γ V :=
  Finset.mem_insert_self _ _

private theorem apex_mem_vectorSpan_coneVertsOn (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    γ ∈ vectorSpan ℝ (coneVertsOn γ V : Set (Fin m → ℝ)) := by
  have h := vsub_mem_vectorSpan ℝ
    (Finset.mem_coe.mpr (add_sum_mem_coneVertsOn γ (Finset.empty_subset V)))
    (Finset.mem_coe.mpr (zero_mem_coneVertsOn γ V))
  rwa [Finset.sum_empty, add_zero, vsub_eq_sub, sub_zero] at h

private theorem label_mem_vectorSpan_coneVertsOn (γ : Fin m → ℝ) {V : Finset (Fin m → ℝ)}
    {v : Fin m → ℝ} (hv : v ∈ V) :
    v ∈ vectorSpan ℝ (coneVertsOn γ V : Set (Fin m → ℝ)) := by
  have h := vsub_mem_vectorSpan ℝ
    (Finset.mem_coe.mpr (add_sum_mem_coneVertsOn γ (Finset.singleton_subset_iff.mpr hv)))
    (Finset.mem_coe.mpr (add_sum_mem_coneVertsOn γ (Finset.empty_subset V)))
  rwa [Finset.sum_singleton, Finset.sum_empty, add_zero, vsub_eq_sub, add_sub_cancel'] at h

/-- Every base-vertex difference from position zero lies in the span of the
oriented caterpillar edges. -/
theorem sub_zero_mem_span_edgeVecs (A : Fin (r + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (i : Fin (r + 1)) :
    A i - A 0 ∈ Submodule.span ℝ (Set.range (edgeVecs A S)) := by
  let U := Submodule.span ℝ (Set.range (edgeVecs A S))
  have hall : ∀ k : ℕ, ∀ hk : k < r + 1, A ⟨k, hk⟩ - A 0 ∈ U := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        have hzero : (⟨0, hk⟩ : Fin (r + 1)) = 0 := Fin.ext rfl
        rw [hzero, sub_self]
        exact Submodule.zero_mem U
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        have hj : j < r := by omega
        let q : Fin r := ⟨j, hj⟩
        let c : Fin (r + 1) := q.succ
        let p : Fin (r + 1) := parent S c
        have hpc : p < c := parent_lt (Fin.succ_pos q)
        have hp : A p - A 0 ∈ U := ih p.val (by
          simpa only [p, c, q, Fin.val_succ] using hpc) p.isLt
        have he : edgeVecs A S q ∈ U :=
          Submodule.subset_span (Set.mem_range_self q)
        have hsub := Submodule.sub_mem U hp he
        change A c - A 0 ∈ U
        convert hsub using 1
        simp only [edgeVecs, p, c, q]
        funext x
        simp only [Pi.sub_apply]
        ring
  exact hall i.val i.isLt

private theorem toR_vtx_eq_stdVerts (n : ℕ) :
    (fun a : Fin (n + 1) => toR (vtx a)) = ParamidGeom.KuhnRhoAux.stdVerts n := by
  funext a
  refine Fin.cases ?_ (fun i => ?_) a
  · rw [vtx_zero, ParamidGeom.KuhnRhoAux.stdVerts_zero]
    funext j
    norm_num [toR]
  · rw [vtx_succ, ParamidGeom.KuhnRhoAux.stdVerts_succ]
    funext j
    simp only [toR, Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]

/-- Differences from one vertex to all remaining permuted simplex vertices
are linearly independent. -/
theorem simplex_differences_linearIndependent
    (π : Equiv.Perm (Fin (r + 1 + 1))) :
    LinearIndependent ℝ (fun i : Fin (r + 1) =>
      toR (vtx (π i.succ)) - toR (vtx (π 0))) := by
  let p : Fin (r + 1 + 1) → Fin (r + 1) → ℝ := fun a => toR (vtx (π a))
  have hp : AffineIndependent ℝ p := by
    have h := (ParamidGeom.KuhnRhoAux.stdVerts_affineIndependent (r + 1)).comp_embedding
      π.toEmbedding
    rw [← toR_vtx_eq_stdVerts (r + 1)] at h
    exact h
  have hli := (affineIndependent_iff_linearIndependent_vsub ℝ p 0).mp hp
  let e : Fin (r + 1) → {a : Fin (r + 1 + 1) // a ≠ 0} :=
    fun i => ⟨i.succ, Fin.succ_ne_zero i⟩
  have he : Function.Injective e := by
    intro i j h
    exact Fin.succ_injective (r + 1) (congrArg Subtype.val h)
  have hc := hli.comp e he
  change LinearIndependent ℝ (fun i : Fin (r + 1) => p i.succ - p 0) at hc
  exact hc

/-- Every word cone in the explicit formula is full-dimensional. -/
theorem fullDimensionalWords (r : ℕ) : FullDimensionalWords r := by
  intro w
  let U := vectorSpan ℝ
    (coneVertsOn (wordGamma w) (wordLabels w) : Set (Fin (r + 1) → ℝ))
  let B : Fin (r + 1) → Fin (r + 1) → ℝ :=
    fun i => wordBase w i - wordApex w
  have hedge : ∀ j : Fin r, edgeVecs (wordBase w) w.2.1 j ∈ U := by
    intro j
    apply label_mem_vectorSpan_coneVertsOn (wordGamma w)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hspan : Submodule.span ℝ (Set.range (edgeVecs (wordBase w) w.2.1)) ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hedge j
  have hγ : wordGamma w ∈ U :=
    apex_mem_vectorSpan_coneVertsOn (wordGamma w) (wordLabels w)
  have hdiff : ∀ i : Fin (r + 1), wordBase w i - wordBase w 0 ∈ U := by
    intro i
    exact hspan (sub_zero_mem_span_edgeVecs (wordBase w) w.2.1 i)
  have hB0 : B 0 ∈ U := by
    have hlast := hdiff (lastHead w.2.1)
    have hsub := Submodule.sub_mem U hγ hlast
    convert hsub using 1
    dsimp [B, wordGamma]
    funext x
    simp only [Pi.sub_apply]
    ring
  have hB : ∀ i, B i ∈ U := by
    intro i
    have hadd := Submodule.add_mem U hB0 (hdiff i)
    convert hadd using 1
    dsimp [B]
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    ring
  have hLI : LinearIndependent ℝ B := by
    dsimp [B, wordBase, wordApex]
    exact simplex_differences_linearIndependent w.1
  have hle : Submodule.span ℝ (Set.range B) ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hB i
  change FiniteDimensional.finrank ℝ U = r + 1
  apply le_antisymm
  · simpa only [FiniteDimensional.finrank_fin_fun] using Submodule.finrank_le U
  · calc
      r + 1 = FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range B)) := by
        rw [finrank_span_eq_card hLI, Fintype.card_fin]
      _ ≤ FiniteDimensional.finrank ℝ U := Submodule.finrank_mono hle

end MaxNN.Caterpillar.Corrections
