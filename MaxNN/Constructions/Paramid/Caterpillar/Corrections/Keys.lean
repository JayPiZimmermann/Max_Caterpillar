import MaxNN.Constructions.Paramid.Geom.Faces.Cone

/-!
# A finite dictionary containing every face correction of a real paramid cone

The caterpillar edges are oriented differences of simplex vertices, so it is
more convenient to retain their real orientation than to choose signs for
positive roots.  A face key records the translated apex and the labels which
remain active.  The three states of a label are: frozen at zero, frozen at the
identity, and active.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom

variable {n : ℕ}

/-- A paramid cone key with real, oriented labels. -/
abbrev RealKey (n : ℕ) := (Fin n → ℝ) × Finset (Fin n → ℝ)

/-- Extend a three-state labelling by zero away from its finite label set. -/
noncomputable def keyExt (V : Finset (Fin n → ℝ)) (τ : V → Fin 3) (v : Fin n → ℝ) : Fin 3 :=
  if h : v ∈ V then τ ⟨v, h⟩ else 0

/-- The face key specified by a three-state labelling. -/
noncomputable def faceKey (γ : Fin n → ℝ) (V : Finset (Fin n → ℝ))
    (τ : V → Fin 3) : RealKey n :=
  (γ + ∑ v in V.filter (fun v => keyExt V τ v = 1), v,
    V.filter fun v => keyExt V τ v = 2)

/-- All cone-face keys of a real paramid cone. -/
noncomputable def faceKeys (γ : Fin n → ℝ) (V : Finset (Fin n → ℝ)) : Finset (RealKey n) :=
  Finset.univ.image (faceKey γ V)

theorem keyExt_of_mem {V : Finset (Fin n → ℝ)} (τ : V → Fin 3) {v : Fin n → ℝ}
    (hv : v ∈ V) : keyExt V τ v = τ ⟨v, hv⟩ := by
  unfold keyExt
  rw [dif_pos hv]

/-- Every pair of disjoint frozen/active label sets occurs in `faceKeys`. -/
theorem mem_faceKeys_of_disjoint {γ : Fin n → ℝ} {V P Z : Finset (Fin n → ℝ)}
    (hP : P ⊆ V) (hZ : Z ⊆ V) (hPZ : Disjoint P Z) :
    (γ + ∑ v in P, v, Z) ∈ faceKeys γ V := by
  let τ : V → Fin 3 := fun v => if v.1 ∈ P then 1 else if v.1 ∈ Z then 2 else 0
  have hτ : ∀ v, v ∈ V → keyExt V τ v = if v ∈ P then 1 else if v ∈ Z then 2 else 0 :=
    fun _ h => keyExt_of_mem τ h
  have h1 : V.filter (fun v => keyExt V τ v = 1) = P := by
    ext v
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hvV, hv⟩
      rw [hτ v hvV] at hv
      by_contra hvP
      rw [if_neg hvP] at hv
      by_cases hvZ : v ∈ Z
      · rw [if_pos hvZ] at hv
        exact absurd hv (by decide)
      · rw [if_neg hvZ] at hv
        exact absurd hv (by decide)
    · intro hvP
      refine ⟨hP hvP, ?_⟩
      rw [hτ v (hP hvP), if_pos hvP]
  have h2 : V.filter (fun v => keyExt V τ v = 2) = Z := by
    ext v
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hvV, hv⟩
      rw [hτ v hvV] at hv
      by_cases hvP : v ∈ P
      · rw [if_pos hvP] at hv
        exact absurd hv (by decide)
      · rw [if_neg hvP] at hv
        by_contra hvZ
        rw [if_neg hvZ] at hv
        exact absurd hv (by decide)
    · intro hvZ
      refine ⟨hZ hvZ, ?_⟩
      have hvP : v ∉ P := fun hvP => Finset.disjoint_left.mp hPZ hvP hvZ
      rw [hτ v (hZ hvZ), if_neg hvP, if_pos hvZ]
  refine Finset.mem_image.mpr ⟨τ, Finset.mem_univ τ, ?_⟩
  unfold faceKey
  rw [h1, h2]

/-- The original cone is one of its own face keys. -/
theorem self_mem_faceKeys (γ : Fin n → ℝ) (V : Finset (Fin n → ℝ)) :
    (γ, V) ∈ faceKeys γ V := by
  have h := mem_faceKeys_of_disjoint (γ := γ) (Finset.empty_subset V)
    (Finset.Subset.refl V) (Finset.disjoint_empty_left V)
  rwa [Finset.sum_empty, add_zero] at h

/-- There are at most three face keys per label. -/
theorem card_faceKeys_le (γ : Fin n → ℝ) (V : Finset (Fin n → ℝ)) :
    (faceKeys γ V).card ≤ 3 ^ V.card := by
  unfold faceKeys
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

/-- A label is usable by the pair-feature layer when it is an oriented
difference of two standard-simplex vertices. -/
def IsSimplexDifference (v : Fin n → ℝ) : Prop :=
  ∃ a b : Fin (n + 1), v = toR (ParamidChain.vtx a) - toR (ParamidChain.vtx b)

end MaxNN.Caterpillar.Corrections
