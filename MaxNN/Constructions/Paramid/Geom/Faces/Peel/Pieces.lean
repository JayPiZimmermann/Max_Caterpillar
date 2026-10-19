import MaxNN.Constructions.Paramid.Geom.Faces.Peel.Annihilator
import MaxNN.Constructions.Paramid.Geom.Flag
import MaxNN.Constructions.Paramid.Geom.Sweep.Support

/-!
# The pieces of the peeled sum (helper of `Geom/Faces/Peel.lean`)

Write `g ∈ LSpan m (d + 1)` as `∑ᵢ bᵢ hS Sᵢ` with nonempty `Sᵢ` of affine dimension `≤ d + 1`
(`exists_hS_decomp`).  The germ of `g` in direction `e` is `∑ᵢ bᵢ hS (face e Sᵢ)`
(`germ_sum_mul_hS`), so for a finite set of directions `e W` the peeled sum
`∑_W germ g (e W) − g` is `∑ᵢ bᵢ (∑_W hS (face (e W) Sᵢ) − hS Sᵢ)`.  One bracket is a *piece*.

* `face_eq_self_of_mem_ann`: a direction annihilating the direction space of `S` has `S` itself
  as face.
* `exists_dot_sub_ne_zero`: a direction that does not annihilate the direction space of `S` is
  not constant on `S`, so its face drops the dimension (`finrank_vectorSpan_face_lt`).
* `peel_piece_mem`: if the directions `e W` (`W ∈ 𝒟`) annihilate `W` and only `W` among the
  members of `𝒟`, and `𝒟` contains the direction space of `S` whenever it has dimension `d + 1`,
  then the piece of `S` lies in `LSpan m d`: for `dim S = d + 1` the term of `W = dir S` cancels
  `hS S` and all other faces are proper; for `dim S ≤ d` every face has dimension `≤ d`.
-/

namespace MaxNN.ParamidGeom.Faces.PeelAux

open BigOperators FiniteDimensional

variable {m : ℕ}

/-! ## Decomposition and germs -/

/-- A function of `LSpan m k` is a finite combination of support functions of nonempty point
sets of affine dimension `≤ k`. -/
theorem exists_hS_decomp {k : ℕ} {g : (Fin m → ℝ) → ℝ} (hg : g ∈ LSpan m k) :
    ∃ (r : ℕ) (b : Fin r → ℝ) (S : Fin r → Finset (Fin m → ℝ)), (∀ i, (S i).Nonempty) ∧
      (∀ i, finrank ℝ (vectorSpan ℝ (S i : Set (Fin m → ℝ))) ≤ k) ∧
      g = fun y => ∑ i, b i * hS (S i) y := by
  obtain ⟨r, b, G, hG⟩ := mem_span_set'.mp hg
  have hS' : ∀ i, ∃ S : Finset (Fin m → ℝ), S.Nonempty ∧
      finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) ≤ k ∧
      (G i : (Fin m → ℝ) → ℝ) = hS S :=
    fun i => Sweep.eq_hS_of_mem_lowerDimSupport (G i).2
  choose S hne hdim heq using hS'
  refine ⟨r, b, S, hne, hdim, ?_⟩
  rw [← hG]
  funext y
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, heq i, smul_eq_mul]

/-- The germ of `∑ᵢ bᵢ hS Sᵢ` in direction `e` is `∑ᵢ bᵢ hS (face e Sᵢ)`. -/
theorem germ_sum_mul_hS {r : ℕ} (b : Fin r → ℝ) (S : Fin r → Finset (Fin m → ℝ))
    (hne : ∀ i, (S i).Nonempty) (e : Fin m → ℝ) :
    germ (fun y => ∑ i, b i * hS (S i) y) e = fun y => ∑ i, b i * hS (face e (S i)) y :=
  germ_eq_of_isGerm (IsGerm.sum Finset.univ fun i _ => (isGerm_hS (hne i) e).const_mul (b i))

/-! ## Faces in annihilating and non-annihilating directions -/

/-- A direction annihilating the direction space of `S` has `S` itself as face. -/
theorem face_eq_self_of_mem_ann {S : Finset (Fin m → ℝ)} {e : Fin m → ℝ}
    (he : e ∈ ann (vectorSpan ℝ (S : Set (Fin m → ℝ)))) : face e S = S :=
  face_eq_self_of_orth fun p hp q hq => mem_ann.mp he (p - q) (by
    rw [← vsub_eq_sub]
    exact vsub_mem_vectorSpan ℝ (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq))

/-- A direction that does not annihilate the direction space of `S` is not constant on `S`. -/
theorem exists_dot_sub_ne_zero {S : Finset (Fin m → ℝ)} {e w : Fin m → ℝ}
    (hw : w ∈ vectorSpan ℝ (S : Set (Fin m → ℝ))) (hew : dot e w ≠ 0) :
    ∃ p ∈ S, ∃ q ∈ S, dot e (p - q) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hew
  have hle : vectorSpan ℝ (S : Set (Fin m → ℝ)) ≤ LinearMap.ker (SupportCut.dotL e) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro x ⟨p, q, hp, hq, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, SupportCut.dotL_apply]
    show dot e (p - q) = 0
    exact h p hp q hq
  have h' := hle hw
  rwa [LinearMap.mem_ker, SupportCut.dotL_apply] at h'

/-! ## One piece -/

/-- **One piece of the peeled sum is lower-dimensional.**  Let the directions `e W` (`W ∈ 𝒟`)
annihilate `W` and no other member of `𝒟`, and let `𝒟` contain the direction space of `S`
whenever it has dimension `d + 1`.  For a nonempty `S` of affine dimension `≤ d + 1`, the piece
`∑_{W ∈ 𝒟} hS (face (e W) S) − hS S` lies in `LSpan m d`. -/
theorem peel_piece_mem {𝒟 : Finset (Submodule ℝ (Fin m → ℝ))} {d : ℕ}
    {e : Submodule ℝ (Fin m → ℝ) → Fin m → ℝ} (heW : ∀ W ∈ 𝒟, e W ∈ ann W)
    (hesep : ∀ W ∈ 𝒟, ∀ W' ∈ 𝒟, W' ≠ W → ∃ w ∈ W', dot (e W) w ≠ 0)
    {S : Finset (Fin m → ℝ)} (hne : S.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) ≤ d + 1)
    (hmem : finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) = d + 1 →
      vectorSpan ℝ (S : Set (Fin m → ℝ)) ∈ 𝒟) :
    (fun y => ∑ W in 𝒟, hS (face (e W) S) y - hS S y) ∈ LSpan m d := by
  classical
  rcases Nat.lt_or_ge (finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ)))) (d + 1) with hlt | hge
  · -- `dim S ≤ d`: every face of `S` has dimension `≤ d`
    have hle : finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) ≤ d := Nat.lt_succ_iff.mp hlt
    have e1 : (fun y => ∑ W in 𝒟, hS (face (e W) S) y - hS S y) =
        (∑ W in 𝒟, hS (face (e W) S)) - hS S := by
      funext y
      rw [Pi.sub_apply, Finset.sum_apply]
    rw [e1]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun W _ => ?_) (Sweep.hS_mem_LSpan hne hle)
    exact Sweep.hS_mem_LSpan (face_nonempty hne _)
      (le_trans (finrank_vectorSpan_face_le _ _) hle)
  · -- `dim S = d + 1`: the term of `W₀ = dir S` cancels `hS S`, the other faces are proper
    have heq : finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) = d + 1 := le_antisymm hdim hge
    have hW₀ := hmem heq
    have e1 : (fun y => ∑ W in 𝒟, hS (face (e W) S) y - hS S y) =
        ∑ W in 𝒟.erase (vectorSpan ℝ (S : Set (Fin m → ℝ))), hS (face (e W) S) := by
      funext y
      rw [← Finset.add_sum_erase 𝒟 _ hW₀, face_eq_self_of_mem_ann (heW _ hW₀),
        Finset.sum_apply]
      ring
    rw [e1]
    refine Submodule.sum_mem _ fun W hW => ?_
    obtain ⟨hWne, hW𝒟⟩ := Finset.mem_erase.mp hW
    obtain ⟨w, hw, hdot⟩ := hesep W hW𝒟 _ hW₀ (Ne.symm hWne)
    have hlt := finrank_vectorSpan_face_lt hne (exists_dot_sub_ne_zero hw hdot)
    rw [heq] at hlt
    exact Sweep.hS_mem_LSpan (face_nonempty hne _) (Nat.lt_succ_iff.mp hlt)

end MaxNN.ParamidGeom.Faces.PeelAux
