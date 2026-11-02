import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Core
import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Recovery
import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Permutation

/-! # Actual inverse parameters of the canonical star physical chart -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65

/-- The forward input-coordinate change on actual readout coefficients. -/
noncomputable def scaleCoefficients (r : ℝ) (a : Fin 4→ℝ) : Fin 4→ℝ :=
  ![r*a 0,a 1,a 2,r*a 3]

lemma unscale_scaleCoefficients {r : ℝ} (hr : 0<r) (a : Fin 4→ℝ) :
    unscaleCoefficients r (scaleCoefficients r a)=a := by
  funext n
  fin_cases n
  · change (r*a 0)/r=a 0
    field_simp [ne_of_gt hr] <;> ring
  · change a 1=a 1
    rfl
  · change a 2=a 2
    rfl
  · change (r*a 3)/r=a 3
    field_simp [ne_of_gt hr] <;> ring

lemma scale_unscaleCoefficients {r : ℝ} (hr : 0<r) (a : Fin 4→ℝ) :
    scaleCoefficients r (unscaleCoefficients r a)=a := by
  funext n
  fin_cases n
  · change r*(a 0/r)=a 0
    exact mul_div_cancel' (a 0) (ne_of_gt hr)
  · change a 1=a 1
    rfl
  · change a 2=a 2
    rfl
  · change r*(a 3/r)=a 3
    exact mul_div_cancel' (a 3) (ne_of_gt hr)

lemma scaleCoefficients_readout {r : ℝ} (hr : 0<r) (a : Fin 4→ℝ) (q v w : ℝ) :
    (coefficientReadout 1 (scaleCoefficients r a) : InvariantState→ℝ) (q,v,w)=
      starLinearForm r (a 0) (a 1) (a 2) (a 3) (r*q) v w := by
  have hq : max 0 (r*q)=r*max 0 q := relu_mul_pos hr q
  have ht : max 0 (r*q+r*v)=r*max 0 (q+v) := by
    rw [← mul_add]
    exact relu_mul_pos hr (q+v)
  change (r*a 0)*max 0 q+a 1*max 0 v+a 2*max 0 w+(r*a 3)*max 0 (q+1*v)=_
  unfold starLinearForm
  rw [hq,ht,one_mul]
  ring

noncomputable def originalHeadRow (net : Network 4 6 5) (j : Fin 5) : Fin 4→ℝ :=
  ![net.W₂ j 0,net.W₂ j 1,net.W₂ j 2,net.W₂ j 3]

/-- Every extracted chart intercept uses the four original physical head weights. -/
noncomputable def extractedHeads {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) : HeadTopology.Data (featureSpace 1) :=
  (![net.W₂ F.positiveHead 4,net.W₂ F.positiveHead 5,
    net.W₂ F.negativeHead 4,net.W₂ F.negativeHead 5],
    coefficientReadout 1 (scaleCoefficients r (originalHeadRow net F.positiveHead)),
    coefficientReadout 1 (scaleCoefficients r (originalHeadRow net F.negativeHead)))

lemma extractedHeads_eval {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) (hr : 0<r) (q v w z : ℝ) :
    (HeadTopology.toHeads (extractedHeads F)).eval (q,v,w) z=
      (actualHeads net r F.positiveHead F.negativeHead).eval (r*q,v,w) z := by
  have hA := scaleCoefficients_readout hr (originalHeadRow net F.positiveHead) q v w
  have hB := scaleCoefficients_readout hr (originalHeadRow net F.negativeHead) q v w
  change Mixed65.Heads.eval (HeadTopology.toHeads (extractedHeads F)) (q,v,w) z=_
  dsimp only [Mixed65.Heads.eval,HeadTopology.toHeads,extractedHeads,actualHeads]
  change relu (net.W₂ F.positiveHead 4*relu z+net.W₂ F.positiveHead 5*relu (-z)+
      (coefficientReadout 1 (scaleCoefficients r (originalHeadRow net F.positiveHead)) :
        InvariantState→ℝ) (q,v,w))-
    relu (net.W₂ F.negativeHead 4*relu z+net.W₂ F.negativeHead 5*relu (-z)+
      (coefficientReadout 1 (scaleCoefficients r (originalHeadRow net F.negativeHead)) :
        InvariantState→ℝ) (q,v,w))=_
  rw [hA,hB]
  rfl

/-- The actual original W signs are the three binary chart orientations. -/
noncomputable def coreOrientation {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) (i : Fin 3) : Bool := by
  classical
  exact if 0<(F.core.reindex F.order).W i then true else false

lemma unit_core_W {net : Network 4 6 5} {r : ℝ} (F : PhysicalNormalForm net r)
    (i : Fin 3) : (F.core.reindex F.order).W i = -1 ∨ (F.core.reindex F.order).W i=1 := by
  by_cases h : (F.core.reindex F.order).W i<0
  · exact Or.inl (by simpa only [if_pos h] using F.orientations i)
  · exact Or.inr (by simpa only [if_neg h] using F.orientations i)

lemma coreOrientation_factor {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) (i : Fin 3) :
    -(F.core.reindex F.order).W i=orientation (coreOrientation F i) := by
  classical
  rw [orientation_factor_of_unit (unit_core_W F i)]
  by_cases h : 0<(F.core.reindex F.order).W i <;>
    simp [coreOrientation,h,orientation]

lemma coreOrientation_flipValue {net : Network 4 6 5} {r : ℝ}
    (F : PhysicalNormalForm net r) (i : Fin 3) :
    flipValue (coreOrientation F i)=
      if 0<(F.core.reindex F.order).W i then 1 else 0 := by
  classical
  by_cases h : 0<(F.core.reindex F.order).W i <;>
    simp [coreOrientation,h,flipValue]

lemma branchIRows_eq_unscale (p : ResidualBase 0) (i : Fin 3) :
    branchIRows p.val.1 p.val.2 i=unscaleCoefficients p.val.1 (coreRowsI p i) := by
  funext n
  fin_cases i <;> fin_cases n <;> norm_num [branchIRows,coreRowsI,unscaleCoefficients]
  all_goals field_simp [ne_of_gt p.property.1]
  all_goals first | rfl | ring

lemma branchIIRows_eq_unscale (p : ResidualBase (-1)) (i : Fin 3) :
    branchIIRows p.val.1 p.val.2 i=unscaleCoefficients p.val.1 (coreRowsII p i) := by
  funext n
  fin_cases i <;> fin_cases n <;> norm_num [branchIIRows,coreRowsII,unscaleCoefficients]
  all_goals field_simp [ne_of_gt p.property.1]
  all_goals ring
end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
