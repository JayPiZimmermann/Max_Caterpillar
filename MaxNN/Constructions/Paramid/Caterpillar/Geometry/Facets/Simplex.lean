import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Facets.Pattern
import MaxNN.Constructions.Paramid.Geom.Defs

/-! # Facet patterns for actual simplex words

The edge-vector injectivity required by the general facet theorem is proved
here from the actual reduced simplex coordinates. In particular, the final
permutation-word theorem has no assumed geometric independence hypothesis.
-/

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {m r : ℕ}

/-- A nonzero oriented difference of simplex vertices determines both ends. -/
theorem simplex_difference_endpoints {a b c d : Fin (m + 1)} (hab : a ≠ b)
    (he : toR (vtx a) - toR (vtx b) = toR (vtx c) - toR (vtx d)) : a = c ∧ b = d := by
  have hint : vtx a - vtx b = vtx c - vtx d := by
    apply ParamidGeom.toR_injective
    funext i
    have hi := congrFun he i
    simpa only [toR, Pi.sub_apply, Int.cast_sub] using hi
  have hfull := congrArg Subtype.val ((reduceEquiv m).injective
    ((reduceEquiv_root b a).trans (hint.trans (reduceEquiv_root d c).symm)))
  have ha := congrFun hfull a
  have hb := congrFun hfull b
  simp only [Pi.sub_apply] at ha hb
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hab, sub_zero] at ha
  rw [Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same, zero_sub] at hb
  constructor
  · by_contra hac
    rw [Pi.single_eq_of_ne hac] at ha
    by_cases had : a = d
    · rw [had, Pi.single_eq_same] at ha
      norm_num at ha
    · rw [Pi.single_eq_of_ne had] at ha
      norm_num at ha
  · by_contra hbd
    rw [Pi.single_eq_of_ne hbd] at hb
    by_cases hbc : b = c
    · rw [hbc, Pi.single_eq_same] at hb
      norm_num at hb
    · rw [Pi.single_eq_of_ne hbc] at hb
      norm_num at hb

theorem edgeVecs_simplex_injective (v : Fin (r + 1) → Fin (m + 1))
    (hv : Function.Injective v) (S : Finset (Fin (r + 1))) :
    Function.Injective (edgeVecs (fun i => toR (vtx (v i))) S) := by
  intro j k he
  have hne : v (parent S j.succ) ≠ v j.succ :=
    fun h => (ne_of_lt (parent_lt (Fin.succ_pos j))) (hv h)
  have hend := simplex_difference_endpoints hne he
  exact Fin.succ_injective r (hv hend.2)

/-- Generic directions of any injectively labelled simplex caterpillar have
lower-dimensional germs. Edge injectivity is derived, not assumed. -/
theorem germDiff_simplexWord_mem_LSpan_of_no_patterns (hr : 2 ≤ r)
    (apex : Fin m → ℝ) (v : Fin (r + 1) → Fin (m + 1)) (hv : Function.Injective v)
    (S : Finset (Fin (r + 1))) (u : Fin m → ℝ)
    (hblock : ¬ BlockValues apex (fun i => toR (vtx (v i))) u)
    (hbraid : ¬ BraidValues apex (fun i => toR (vtx (v i))) u) :
    germDiff u (caterpillarUnit apex (fun i => toR (vtx (v i))) S) ∈ LSpan m (r - 1) :=
  germDiff_caterpillarUnit_mem_LSpan_of_no_patterns hr apex _ S
    (edgeVecs_simplex_injective v hv S) u hblock hbraid

/-- The concrete reduced-ambient statement for a permutation of all simplex
vertices: the apex is `π 0` and the base word consists of `π 1, ..., π (r+1)`.
There are `r+2` vertices in ambient dimension `r+1`. -/
theorem germDiff_permutationWord_mem_LSpan_of_no_patterns (hr : 2 ≤ r)
    (π : Equiv.Perm (Fin (r + 1 + 1))) (S : Finset (Fin (r + 1))) (u : Fin (r + 1) → ℝ)
    (hblock : ¬ BlockValues (toR (vtx (π 0))) (fun i => toR (vtx (π i.succ))) u)
    (hbraid : ¬ BraidValues (toR (vtx (π 0))) (fun i => toR (vtx (π i.succ))) u) :
    germDiff u (caterpillarUnit (toR (vtx (π 0)))
      (fun i => toR (vtx (π i.succ))) S) ∈ LSpan (r + 1) (r - 1) :=
  germDiff_simplexWord_mem_LSpan_of_no_patterns hr _ (fun i => π i.succ)
    (π.injective.comp (Fin.succ_injective (r + 1))) S u hblock hbraid

end MaxNN.Caterpillar
