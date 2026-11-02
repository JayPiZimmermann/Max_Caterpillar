import MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel.Permutation
import MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel.Reindex
import MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel.Fixed

/-! # Every actual interaction triangle is a relabeled native triangle

The original matrix is arbitrary and ordered. A genuine permutation places a
padded interaction cover in coordinates 012; the remaining two coordinates are
modular. Empty/full normalization implies precisely the native total-zero
constraint. No native representation is presumed in the source hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
open TriangleInterleavings

/-- `e` maps the fixed native labels to the actual original vertices. Thus the
existing inverse-reading relabeling convention uses `e.symm` on the source. -/
theorem booleanQuadratic_triangle_relabel (a : ℝ) (b : Fin 5 → ℝ)
    (d : Fin 5 → Fin 5 → ℝ) (htriangle : TriangleContained (quadraticInteractionGraph d))
    (hEmpty : booleanQuadratic a b d ∅=0)
    (hFull : booleanQuadratic a b d Finset.univ=0) :
    ∃ (e : Equiv.Perm (Fin 5)) (A B C x y z u v : ℝ),
      relabelSetFunction (booleanQuadratic a b d) e.symm=
        nativeTriangle ![A,B,C,x,y,z,u,v] ∧ A+B+C+x+y+z+u+v=0 := by
  obtain ⟨e,he⟩ := triangleContained_permutation (quadraticInteractionGraph d) htriangle
  let b' := fun i => b (e i)
  let d' := fun i j => d (e i) (e j)
  have hsupport : ∀ i j, (quadraticInteractionGraph d').Adj i j → i.val<3 ∧ j.val<3 := by
    intro i j hij
    apply he i j
    change i≠j ∧ effectiveInteraction d (e i) (e j)≠0 at hij
    change e i≠e j ∧ effectiveInteraction d (e i) (e j)≠0
    exact ⟨fun h => hij.1 (e.injective h),hij.2⟩
  have ha : a=0 := by simpa [booleanQuadratic,booleanCoordinate] using hEmpty
  have hfixed := booleanQuadratic_eq_nativeTriangle_fixed a b' d' hsupport ha
  have hrep := (relabel_booleanQuadratic a b d e).trans hfixed
  refine ⟨e,effectiveLinear b' d' 0,effectiveLinear b' d' 1,effectiveLinear b' d' 2,
    effectiveInteraction d' 0 1,effectiveInteraction d' 0 2,effectiveInteraction d' 1 2,
    effectiveLinear b' d' 3,effectiveLinear b' d' 4,hrep,?_⟩
  have hh := congrFun hrep Finset.univ
  rw [relabel_full,hFull,nativeTriangle_full] at hh
  exact hh.symm

end MaxCaterpillar.Frontier.StarCertificate.TriangleRelabel
