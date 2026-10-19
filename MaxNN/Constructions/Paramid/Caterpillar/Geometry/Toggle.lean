import MaxNN.Constructions.Paramid.Caterpillar.Block.Transform
import MaxNN.Constructions.Paramid.Caterpillar.Formula.Simplex
import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Adjacent

/-! # Analytic block pairing for the actual formula indices -/

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

noncomputable def blockUnit (q : BlockIndex r) : (Fin (r + 1) → ℝ) → ℝ :=
  caterpillarUnit (toR (vtx (q.1 0)))
    (fun i : Fin (r + 1) => toR (vtx (q.1 i.succ))) q.2.1

theorem blockWordValues_eq_values (u : Fin (r + 1) → ℝ) (q : BlockIndex r) :
    blockWordValues (simplexValues u) q =
      values (fun i : Fin (r + 1) => toR (vtx (q.1 i.succ))) u := rfl

theorem blockApexValue_eq_dot (u : Fin (r + 1) → ℝ) (q : BlockIndex r) :
    blockApexValue (simplexValues u) q = dot (toR (vtx (q.1 0))) u := rfl

theorem blockUnit_prefixPairAt (q : BlockIndex r) (j : Fin r)
    (ha0 : (0 : Fin (r + 1)) < j.castSucc) (hb : j.succ ∈ q.2.1) :
    blockUnit (prefixPairAt q j ha0 hb) =
      caterpillarUnit (toR (vtx (q.1 0)))
        (fun i : Fin (r + 1) => toR (vtx (q.1 i.succ)))
        (toggleCut j.castSucc q.2.1) := rfl

theorem blockUnit_suffixPairAt (q : BlockIndex r) (j : Fin r)
    (hsize : j.succ.val < r) (ha : j.succ ∈ q.2.1) :
    blockUnit (suffixPairAt q j hsize ha) =
      caterpillarUnit (toR (vtx (q.1 0)))
        (fun i : Fin (r + 1) =>
          toR (vtx (q.1 (adjacentSwap (nextIndex j hsize) i).succ)))
        (toggleCut (nextIndex j hsize).succ q.2.1) := by
  funext y
  unfold blockUnit suffixPairAt
  simp only [suffixPerm_zero, suffixPerm_succ]

theorem germDiff_blockUnit_sub_transform_mem_LSpan_one_of_prefix
    (u : Fin (r + 1) → ℝ) (q : BlockIndex r)
    (hp : ActivePrefix (simplexValues u) q) :
    germDiff u (blockUnit q) - germDiff u (blockUnit (blockTransform (simplexValues u) q)) ∈
      LSpan (r + 1) 1 := by
  obtain ⟨j, ha0, hb, hsplit, hapex⟩ := hp
  rw [blockTransform_eq_prefix (simplexValues u) q j ha0 hb hsplit hapex,
    blockUnit_prefixPairAt]
  let apex := toR (vtx (q.1 0))
  let A := fun i : Fin (r + 1) => toR (vtx (q.1 i.succ))
  have hs : SplitValues (values A u) j := by
    rwa [← blockWordValues_eq_values u q]
  have hap : dot apex u = dot (A j.succ) u := by
    exact hapex
  by_cases hcut : j.castSucc ∈ q.2.1
  · rw [toggleCut, if_pos hcut]
    have hb' : j.succ ∈ q.2.1.erase j.castSucc :=
      Finset.mem_erase.mpr ⟨ne_of_gt (Fin.castSucc_lt_succ j), hb⟩
    have h := germDiff_insert_left_sub_mem_LSpan_one_of_prefix apex A
      (q.2.1.erase j.castSucc) j hb' u hs hap
    rw [Finset.insert_erase hcut] at h
    simpa only [neg_sub] using Submodule.neg_mem (LSpan (r + 1) 1) h
  · rw [toggleCut, if_neg hcut]
    exact germDiff_insert_left_sub_mem_LSpan_one_of_prefix apex A q.2.1 j hb u hs hap

theorem germDiff_blockUnit_sub_transform_mem_LSpan_one_of_suffix
    (u : Fin (r + 1) → ℝ) (q : BlockIndex r)
    (hsuf : ActiveSuffix (simplexValues u) q) :
    germDiff u (blockUnit q) - germDiff u (blockUnit (blockTransform (simplexValues u) q)) ∈
      LSpan (r + 1) 1 := by
  obtain ⟨j, hsize, ha, hsplit, hapex⟩ := hsuf
  rw [blockTransform_eq_suffix (simplexValues u) q j hsize ha hsplit hapex,
    blockUnit_suffixPairAt]
  let k := nextIndex j hsize
  let apex := toR (vtx (q.1 0))
  let A := fun i : Fin (r + 1) => toR (vtx (q.1 i.succ))
  have hjk : k.castSucc = j.succ := nextIndex_castSucc j hsize
  have hs : SplitValues (values A u) j := by
    rwa [← blockWordValues_eq_values u q]
  have hap : dot apex u = dot (A 0) u := by
    exact hapex
  by_cases hcut : k.succ ∈ q.2.1
  · rw [toggleCut, if_pos hcut]
    let A' := fun i => A (adjacentSwap k i)
    have hka : j.succ ∈ q.2.1.erase k.succ := by
      apply Finset.mem_erase.mpr
      refine ⟨?_, ha⟩
      rw [← hjk]
      exact ne_of_lt (Fin.castSucc_lt_succ k)
    have hkb : k.succ ∉ q.2.1.erase k.succ := Finset.not_mem_erase _ _
    have hv : values A' u = values A u := by
      funext i
      change values A u (adjacentSwap k i) = values A u i
      exact hs.next_swap_invariant hsize i
    have hs' : SplitValues (values A' u) j := by rwa [hv]
    have hap' : dot apex u = dot (A' 0) u := by
      change dot apex u = values A' u 0
      rw [hv]
      exact hap
    have h := germDiff_adjacentSwap_insert_right_sub_mem_LSpan_one_of_suffix apex A'
      (q.2.1.erase k.succ) j k hjk hka hkb u hs' hap'
    have hAA : (fun i => A' (adjacentSwap k i)) = A := by
      funext i
      simp [A', adjacentSwap]
    rw [Finset.insert_erase hcut, hAA] at h
    simpa only [neg_sub] using Submodule.neg_mem (LSpan (r + 1) 1) h
  · rw [toggleCut, if_neg hcut]
    exact germDiff_adjacentSwap_insert_right_sub_mem_LSpan_one_of_suffix apex A q.2.1
      j k hjk ha hcut u hs hap

noncomputable def blockGermTerm (u : Fin (r + 1) → ℝ) (q : BlockIndex r) :
    (Fin (r + 1) → ℝ) → ℝ :=
  wordWeight r q.2.1 • germDiff u (blockUnit q)

theorem blockGermTerm_add_transform_mem_LSpan_one_of_prefix
    (u : Fin (r + 1) → ℝ) (q : BlockIndex r)
    (hp : ActivePrefix (simplexValues u) q) :
    blockGermTerm u q + blockGermTerm u (blockTransform (simplexValues u) q) ∈
      LSpan (r + 1) 1 := by
  have hg := germDiff_blockUnit_sub_transform_mem_LSpan_one_of_prefix u q hp
  have hs := Submodule.smul_mem (LSpan (r + 1) 1) (wordWeight r q.2.1) hg
  unfold blockGermTerm
  rw [wordWeight_blockTransform_prefix (simplexValues u) q hp]
  simpa only [smul_sub, smul_add, smul_neg, neg_smul, sub_eq_add_neg] using hs

theorem blockGermTerm_add_transform_mem_LSpan_one_of_suffix
    (u : Fin (r + 1) → ℝ) (q : BlockIndex r)
    (hsuf : ActiveSuffix (simplexValues u) q) :
    blockGermTerm u q + blockGermTerm u (blockTransform (simplexValues u) q) ∈
      LSpan (r + 1) 1 := by
  have hg := germDiff_blockUnit_sub_transform_mem_LSpan_one_of_suffix u q hsuf
  have hs := Submodule.smul_mem (LSpan (r + 1) 1) (wordWeight r q.2.1) hg
  unfold blockGermTerm
  rw [wordWeight_blockTransform_suffix (simplexValues u) q hsuf]
  simpa only [smul_sub, smul_add, smul_neg, neg_smul, sub_eq_add_neg] using hs

end MaxNN.Caterpillar
