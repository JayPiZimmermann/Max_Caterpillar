import MaxNN.Constructions.Paramid.Geom.Faces.Defs
import MaxNN.Constructions.Paramid.Geom.Faces.Peel.Pieces

/-!
# Lemma P: peeling one dimension relative to a subspace

Module L5 of `work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md` (Section 4.3,
Lemma P; target statement in Section 8.1, Group B).

**Lemma P.**  Let `U` be a subspace of `ℝ^m` with `d + 1 < dim U` and `g ∈ LSpan m (d + 1)`.
There is a finite set `E` of directions, none of which annihilates `U`, such that
`∑_{e ∈ E} germ g e − g ∈ LSpan m d` (`exists_peel_rel`).

*Proof.*  Write `g = ∑ᵢ bᵢ hS Sᵢ` with `dim Sᵢ ≤ d + 1` and let `𝒟` be the set of the direction
spaces `W = vectorSpan Sᵢ` of dimension `d + 1`.  For `W ∈ 𝒟` choose `e W` annihilating `W`, not
annihilating `U` and not annihilating any other member of `𝒟` (`PeelAux.exists_sep_dir`: the
subspaces to avoid are proper subspaces of the annihilator of `W`, and a real vector space is no
finite union of proper subspaces).  These directions are pairwise distinct, `E` is their image,
and the germ of `hS Sᵢ` in direction `e` is `hS (face e Sᵢ)`.  So
`∑_{e ∈ E} germ g e − g = ∑ᵢ bᵢ (∑_{W ∈ 𝒟} hS (face (e W) Sᵢ) − hS Sᵢ)`, and every bracket lies in
`LSpan m d` (`PeelAux.peel_piece_mem`): if `dim Sᵢ = d + 1`, the term of `W = vectorSpan Sᵢ` is
`hS Sᵢ` itself and every other face of `Sᵢ` is proper; if `dim Sᵢ ≤ d`, so are all its faces.

Helpers: `Faces/Peel/Generic.lean` (common non-roots, no finite union of proper subspaces),
`Faces/Peel/Annihilator.lean` (annihilators, separating directions), `Faces/Peel/Pieces.lean`
(decomposition, germs, the pieces).
-/

namespace MaxNN.ParamidGeom.Faces

open BigOperators FiniteDimensional PeelAux

variable {m : ℕ}

/-- **Lemma P (peeling relative to `U`).**  If `d + 1 < dim U` and `g ∈ LSpan m (d + 1)`, there
is a finite set `E` of directions, none annihilating `U`, with
`∑_{e ∈ E} germ g e − g ∈ LSpan m d`. -/
theorem exists_peel_rel (U : Submodule ℝ (Fin m → ℝ)) {d : ℕ}
    (hd : d + 1 < FiniteDimensional.finrank ℝ U) {g : (Fin m → ℝ) → ℝ}
    (hg : g ∈ LSpan m (d + 1)) :
    ∃ E : Finset (Fin m → ℝ), (∀ e ∈ E, ∃ w ∈ U, dot e w ≠ 0) ∧
      (fun y => ∑ e in E, germ g e y - g y) ∈ LSpan m d := by
  classical
  obtain ⟨r, b, S, hne, hdim, rfl⟩ := exists_hS_decomp hg
  -- the direction spaces of dimension `d + 1`
  obtain ⟨𝒟, h𝒟⟩ : ∃ 𝒟 : Finset (Submodule ℝ (Fin m → ℝ)), ∀ W, W ∈ 𝒟 ↔
      (∃ i, vectorSpan ℝ (S i : Set (Fin m → ℝ)) = W) ∧ finrank ℝ W = d + 1 :=
    ⟨(Finset.univ.image fun i => vectorSpan ℝ (S i : Set (Fin m → ℝ))).filter
      fun W => finrank ℝ W = d + 1, fun W => by simp [Finset.mem_filter, Finset.mem_image]⟩
  have hrank : ∀ W ∈ 𝒟, finrank ℝ W = d + 1 := fun W hW => ((h𝒟 W).mp hW).2
  -- one separating direction per direction space
  have hsep : ∀ W ∈ 𝒟, ∃ e ∈ ann W, (∃ w ∈ U, dot e w ≠ 0) ∧
      ∀ W' ∈ 𝒟, W' ≠ W → ∃ w ∈ W', dot e w ≠ 0 :=
    fun W hW => exists_sep_dir hrank hW hd
  choose! e heW heU hesep using hsep
  have hinj : ∀ W ∈ 𝒟, ∀ W' ∈ 𝒟, e W = e W' → W = W' := by
    intro W hW W' hW' hWW'
    by_contra hne'
    obtain ⟨w, hw, hdot⟩ := hesep W hW W' hW' (Ne.symm hne')
    rw [hWW'] at hdot
    exact hdot (mem_ann.mp (heW W' hW') w hw)
  refine ⟨𝒟.image e, fun e' he' => ?_, ?_⟩
  · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp he'
    exact heU W hW
  · -- the peeled sum is a combination of pieces
    have key : (fun y => ∑ e' in 𝒟.image e, germ (fun y => ∑ i, b i * hS (S i) y) e' y -
        ∑ i, b i * hS (S i) y) =
        ∑ i, b i • fun y => ∑ W in 𝒟, hS (face (e W) (S i)) y - hS (S i) y := by
      funext y
      rw [Finset.sum_image hinj, Finset.sum_apply]
      simp only [germ_sum_mul_hS b S hne, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_sub, Finset.mul_sum]
    show (fun y => ∑ e' in 𝒟.image e, germ (fun y => ∑ i, b i * hS (S i) y) e' y -
        ∑ i, b i * hS (S i) y) ∈ LSpan m d
    rw [key]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (b i) ?_
    exact peel_piece_mem heW hesep (hne i) (hdim i)
      fun h => (h𝒟 _).mpr ⟨⟨i, rfl⟩, h⟩

end MaxNN.ParamidGeom.Faces
