import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Evaluation
import MaxCaterpillar.Fiber.Count65.Star.HeadBundles

/-! # Actual canonical physical charts for both star residual branches -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65

/-- A set bit reverses the corresponding original core. -/
def flipValue : Bool→ℝ | false => 0 | true => 1
def orientation : Bool→ℝ | false => 1 | true => -1

noncomputable def coreRowsI (p : ResidualBase 0) : Fin 3→Fin 4→ℝ :=
  ![![p.val.1-1,0,-1,1],![p.val.1*p.val.2,1,-1,0],
    ![p.val.1*p.val.2-1,0,-1,1]]
noncomputable def coreRowsII (p : ResidualBase (-1)) : Fin 3→Fin 4→ℝ :=
  ![![p.val.1-1,p.val.2,-1,1],![p.val.1,1,-1,0],
    ![p.val.1,1+p.val.2,-1,0]]

noncomputable def orientedRow (b : Bool) (c : Fin 4→ℝ) : Fin 4→ℝ :=
  fun j => orientation b*c j

abbrev BranchIFiber (o : Fin 3→Bool) :=
  HeadTopology.BundleFiber (featureSpace 1) (fun p : ResidualBase 0 =>
    coefficientReadout 1 (branchICoefficients (flipValue (o 0))
      (flipValue (o 1)) (flipValue (o 2)) p))
abbrev BranchIIFiber (o : Fin 3→Bool) :=
  HeadTopology.BundleFiber (featureSpace 1) (fun p : ResidualBase (-1) =>
    coefficientReadout 1 (branchIICoefficients (flipValue (o 0))
      (flipValue (o 1)) (flipValue (o 2)) p))

/-- Cores occupy physical neurons 0,1,2, heads occupy 3,4. -/
noncomputable def branchIChart (o : Fin 3→Bool) (p : BranchIFiber o) : Network 4 6 5 :=
  headLift p.val.1.val.1 (orientedRow (o 0) (coreRowsI p.val.1 0))
    (orientedRow (o 1) (coreRowsI p.val.1 1))
    (orientedRow (o 2) (coreRowsI p.val.1 2)) p.val.2
noncomputable def branchIIChart (o : Fin 3→Bool) (p : BranchIIFiber o) : Network 4 6 5 :=
  headLift p.val.1.val.1 (orientedRow (o 0) (coreRowsII p.val.1 0))
    (orientedRow (o 1) (coreRowsII p.val.1 1))
    (orientedRow (o 2) (coreRowsII p.val.1 2)) p.val.2

lemma oriented_fold (b : Bool) (t : ℝ) :
    relu (orientation b*t)=relu t-flipValue b*t := by
  cases b
  · simp [orientation,flipValue]
  · simp only [orientation,flipValue,neg_one_mul,one_mul]
    linarith only [relu_sub_relu_neg t]

lemma orientedRow_readout (b : Bool) (c : Fin 4→ℝ) (x : InvariantState) :
    (coefficientReadout 1 (orientedRow b c) : InvariantState→ℝ) x=
      orientation b*(coefficientReadout 1 c : InvariantState→ℝ) x := by
  change _ = orientation b*readout 1 (c 0) (c 1) (c 2) (c 3) x
  unfold coefficientReadout orientedRow readout starLinearForm
  ring

lemma branchI_remainder_readout (i j z : ℝ) (p : ResidualBase 0) (x : InvariantState) :
    (coefficientReadout 1 (branchICoefficients i j z p) : InvariantState→ℝ) x=
      max 0 x.2.2+i*(coefficientReadout 1 (coreRowsI p 0) : InvariantState→ℝ) x+
      j*(coefficientReadout 1 (coreRowsI p 1) : InvariantState→ℝ) x-
      z*(coefficientReadout 1 (coreRowsI p 2) : InvariantState→ℝ) x := by
  change (i*(p.val.1-1)+j*(p.val.1*p.val.2)-z*(p.val.1*p.val.2-1))*max 0 x.1+
      j*max 0 x.2.1+(1-i-j+z)*max 0 x.2.2+(i-z)*max 0 (x.1+1*x.2.1)=_
  change _=max 0 x.2.2+i*((p.val.1-1)*max 0 x.1+0*max 0 x.2.1+
      (-1)*max 0 x.2.2+1*max 0 (x.1+1*x.2.1))+
    j*((p.val.1*p.val.2)*max 0 x.1+1*max 0 x.2.1+(-1)*max 0 x.2.2+
      0*max 0 (x.1+1*x.2.1))-
    z*((p.val.1*p.val.2-1)*max 0 x.1+0*max 0 x.2.1+(-1)*max 0 x.2.2+
      1*max 0 (x.1+1*x.2.1))
  ring

lemma branchII_remainder_readout (i j z : ℝ) (p : ResidualBase (-1)) (x : InvariantState) :
    (coefficientReadout 1 (branchIICoefficients i j z p) : InvariantState→ℝ) x=
      max 0 x.2.2+i*(coefficientReadout 1 (coreRowsII p 0) : InvariantState→ℝ) x+
      j*(coefficientReadout 1 (coreRowsII p 1) : InvariantState→ℝ) x-
      z*(coefficientReadout 1 (coreRowsII p 2) : InvariantState→ℝ) x := by
  change (i*(p.val.1-1)+j*p.val.1-z*p.val.1)*max 0 x.1+
      (i*p.val.2+j-z*(1+p.val.2))*max 0 x.2.1+(1-i-j+z)*max 0 x.2.2+
      i*max 0 (x.1+1*x.2.1)=_
  change _=max 0 x.2.2+i*((p.val.1-1)*max 0 x.1+p.val.2*max 0 x.2.1+
      (-1)*max 0 x.2.2+1*max 0 (x.1+1*x.2.1))+
    j*(p.val.1*max 0 x.1+1*max 0 x.2.1+(-1)*max 0 x.2.2+
      0*max 0 (x.1+1*x.2.1))-
    z*(p.val.1*max 0 x.1+(1+p.val.2)*max 0 x.2.1+(-1)*max 0 x.2.2+
      0*max 0 (x.1+1*x.2.1))
  ring

lemma coreRowsI_readout (p : ResidualBase 0) (q v w : ℝ) :
    (coefficientReadout 1 (coreRowsI p 0) : InvariantState→ℝ) (q,v,w)=
        comparison p.val.1 (p.val.1*q) v-max 0 w ∧
    (coefficientReadout 1 (coreRowsI p 1) : InvariantState→ℝ) (q,v,w)=
        max 0 v-max 0 w+p.val.2*max 0 (p.val.1*q) ∧
    (coefficientReadout 1 (coreRowsI p 2) : InvariantState→ℝ) (q,v,w)=
        comparison p.val.1 (p.val.1*q) v-max 0 (p.val.1*q)-max 0 w+
          p.val.2*max 0 (p.val.1*q) := by
  rw [comparison_rescale p.property.1,
    show max 0 (p.val.1*q)=p.val.1*max 0 q from relu_mul_pos p.property.1 q]
  change ((p.val.1-1)*max 0 q+0*max 0 v+(-1)*max 0 w+1*max 0 (q+1*v)=_) ∧
    ((p.val.1*p.val.2)*max 0 q+1*max 0 v+(-1)*max 0 w+0*max 0 (q+1*v)=_) ∧
    ((p.val.1*p.val.2-1)*max 0 q+0*max 0 v+(-1)*max 0 w+1*max 0 (q+1*v)=_)
  simp only [one_mul,relu]
  constructor
  · ring
  constructor <;> ring

lemma coreRowsII_readout (p : ResidualBase (-1)) (q v w : ℝ) :
    (coefficientReadout 1 (coreRowsII p 0) : InvariantState→ℝ) (q,v,w)=
        comparison p.val.1 (p.val.1*q) v-max 0 w+p.val.2*max 0 v ∧
    (coefficientReadout 1 (coreRowsII p 1) : InvariantState→ℝ) (q,v,w)=
        max 0 (p.val.1*q)+max 0 v-max 0 w ∧
    (coefficientReadout 1 (coreRowsII p 2) : InvariantState→ℝ) (q,v,w)=
        max 0 (p.val.1*q)+(1+p.val.2)*max 0 v-max 0 w := by
  rw [comparison_rescale p.property.1,
    show max 0 (p.val.1*q)=p.val.1*max 0 q from relu_mul_pos p.property.1 q]
  change ((p.val.1-1)*max 0 q+p.val.2*max 0 v+(-1)*max 0 w+1*max 0 (q+1*v)=_) ∧
    (p.val.1*max 0 q+1*max 0 v+(-1)*max 0 w+0*max 0 (q+1*v)=_) ∧
    (p.val.1*max 0 q+(1+p.val.2)*max 0 v+(-1)*max 0 w+0*max 0 (q+1*v)=_)
  simp only [one_mul,relu]
  constructor
  · ring
  constructor <;> ring

private lemma target_shift (x : Point 4) :
    x 2+max (max 0 ((x 0-x 1)+(x 1-x 2))) (max (x 1-x 2) (x 3-x 2))=Maximum 4 x := by
  calc
    _ = max (max (x 2) (x 0)) (max (x 1) (x 3)) := by
      rw [← max_add_add_left,← max_add_add_left,← max_add_add_left]
      congr 2 <;> ring
    _ = Maximum 4 x := by rw [Maximum_four]; ac_rfl

/-- Every point of the entire first chart is an actual exact Max4 network. -/
theorem branchIChart_eval (o : Fin 3→Bool) (p : BranchIFiber o) (x : Point 4) :
    (branchIChart o p).eval x=Maximum 4 x := by
  let b := p.val.1
  let s := invariantState b.val.1 x
  have hr : 0<b.val.1 := b.property.1
  have hq : b.val.1*((x 0-x 1)/b.val.1)=x 0-x 1 := by
    exact mul_div_cancel' (x 0-x 1) (ne_of_gt hr)
  have hc := coreRowsI_readout b s.1 s.2.1 s.2.2
  have hres : max 0 s.2.2+
      relu ((coefficientReadout 1 (coreRowsI b 0) : InvariantState→ℝ) s)+
      relu ((coefficientReadout 1 (coreRowsI b 1) : InvariantState→ℝ) s)-
      relu ((coefficientReadout 1 (coreRowsI b 2) : InvariantState→ℝ) s)=
      max (max 0 ((x 0-x 1)+(x 1-x 2))) (max (x 1-x 2) (x 3-x 2)) := by
    rw [hc.1,hc.2.1,hc.2.2]
    dsimp only [s,invariantState]
    rw [hq]
    change branchI b.val.1 b.val.2 (x 0-x 1) (x 1-x 2) (x 3-x 2)=_
    exact branchI_eq_max hr b.property.2.1 b.property.2.2 _ _ _
  rw [branchIChart,headLift_eval hr]
  simp_rw [orientedRow_readout,oriented_fold]
  have hh := p.property s (x 2)
  rw [hh,branchI_remainder_readout]
  rw [← target_shift x]
  change _ = x 2+_
  linear_combination hres

/-- Every point of the entire second chart is an actual exact Max4 network. -/
theorem branchIIChart_eval (o : Fin 3→Bool) (p : BranchIIFiber o) (x : Point 4) :
    (branchIIChart o p).eval x=Maximum 4 x := by
  let b := p.val.1
  let s := invariantState b.val.1 x
  have hr : 0<b.val.1 := b.property.1
  have hq : b.val.1*((x 0-x 1)/b.val.1)=x 0-x 1 := by
    exact mul_div_cancel' (x 0-x 1) (ne_of_gt hr)
  have hc := coreRowsII_readout b s.1 s.2.1 s.2.2
  have hres : max 0 s.2.2+
      relu ((coefficientReadout 1 (coreRowsII b 0) : InvariantState→ℝ) s)+
      relu ((coefficientReadout 1 (coreRowsII b 1) : InvariantState→ℝ) s)-
      relu ((coefficientReadout 1 (coreRowsII b 2) : InvariantState→ℝ) s)=
      max (max 0 ((x 0-x 1)+(x 1-x 2))) (max (x 1-x 2) (x 3-x 2)) := by
    rw [hc.1,hc.2.1,hc.2.2]
    dsimp only [s,invariantState]
    rw [hq]
    change branchII b.val.1 b.val.2 (x 0-x 1) (x 1-x 2) (x 3-x 2)=_
    exact branchII_eq_max hr b.property.2.1 b.property.2.2 _ _ _
  rw [branchIIChart,headLift_eval hr]
  simp_rw [orientedRow_readout,oriented_fold]
  have hh := p.property s (x 2)
  rw [hh,branchII_remainder_readout]
  rw [← target_shift x]
  change _ = x 2+_
  linear_combination hres

lemma continuous_coreRowsI : Continuous coreRowsI := by
  have hr : Continuous (fun p : ResidualBase 0 => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hk : Continuous (fun p : ResidualBase 0 => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  apply continuous_pi
  intro i
  fin_cases i
  all_goals apply continuous_pi
  all_goals intro j
  all_goals fin_cases j
  all_goals first | exact continuous_const | exact hr.sub continuous_const | exact hr.mul hk | exact (hr.mul hk).sub continuous_const

lemma continuous_coreRowsII : Continuous coreRowsII := by
  have hr : Continuous (fun p : ResidualBase (-1) => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hh : Continuous (fun p : ResidualBase (-1) => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  apply continuous_pi
  intro i
  fin_cases i
  all_goals apply continuous_pi
  all_goals intro j
  all_goals fin_cases j
  all_goals first | exact continuous_const | exact hr.sub continuous_const | exact hr | exact hh | exact continuous_const.add hh

lemma continuous_orientedRow {β : Type*} [TopologicalSpace β]
    (b : Bool) (f : β→Fin 4→ℝ) (hf : Continuous f) :
    Continuous (fun p => orientedRow b (f p)) := by
  apply continuous_pi
  intro j
  exact continuous_const.mul ((continuous_apply j).comp hf)

/-- The first physical chart is continuous on its complete parameter fiber. -/
theorem continuous_branchIChart (o : Fin 3→Bool) : Continuous (branchIChart o) := by
  have hb : Continuous (fun p : BranchIFiber o => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hr : Continuous (fun p : BranchIFiber o => p.val.1.val.1) :=
    (continuous_fst.comp continuous_subtype_val).comp hb
  have hc (i : Fin 3) : Continuous (fun p : BranchIFiber o => coreRowsI p.val.1 i) :=
    (continuous_apply i).comp (continuous_coreRowsI.comp hb)
  exact continuous_headLift _ _ _ _ _ hr
    (continuous_orientedRow (o 0) _ (hc 0))
    (continuous_orientedRow (o 1) _ (hc 1))
    (continuous_orientedRow (o 2) _ (hc 2))
    (continuous_snd.comp continuous_subtype_val) (fun p => p.val.1.property.1)

/-- The second physical chart is continuous including r=1 and slack=-1. -/
theorem continuous_branchIIChart (o : Fin 3→Bool) : Continuous (branchIIChart o) := by
  have hb : Continuous (fun p : BranchIIFiber o => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hr : Continuous (fun p : BranchIIFiber o => p.val.1.val.1) :=
    (continuous_fst.comp continuous_subtype_val).comp hb
  have hc (i : Fin 3) : Continuous (fun p : BranchIIFiber o => coreRowsII p.val.1 i) :=
    (continuous_apply i).comp (continuous_coreRowsII.comp hb)
  exact continuous_headLift _ _ _ _ _ hr
    (continuous_orientedRow (o 0) _ (hc 0))
    (continuous_orientedRow (o 1) _ (hc 1))
    (continuous_orientedRow (o 2) _ (hc 2))
    (continuous_snd.comp continuous_subtype_val) (fun p => p.val.1.property.1)
end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
