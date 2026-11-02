import MaxCaterpillar.Fiber.Count65.Star.PhysicalNormalForm
import MaxCaterpillar.Fiber.Count65.Topology

/-! # Closed coefficient tests on actual normalized star networks

The parameter includes r=1. Every class is defined by equations or weak
inequalities on actual physical weights and all-real head intercepts.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Fiber.Count65.ActualStarLabels
open Set Function Star Star65 MaxCaterpillar.Frontier

abbrev Slice := {p : ℝ × Network 4 6 5 //
  0 < p.1 ∧ p.1 ≤ 1 ∧ p.2.W₁=firstRows p.1 ∧
    (∀ x, p.2.eval x=Maximum 4 x) ∧ (∀ i,p.2.w₃ i=1 ∨ p.2.w₃ i = -1)}
abbrev Label := Equiv.Perm (Fin 5) × NonpairedLabel

def rowOrder (l : Label) := l.1
def branch (l : Label) := l.2.1
def orientations (l : Label) := l.2.2.1
def signed (l : Label) := l.2.2.2
noncomputable def eps (bits : Fin 3 → Bool) (i : Fin 3) : ℝ := if bits i then -1 else 1

/-- Physical charts use the opposite bit: true reverses a canonical W=-1 core. -/
def chartFlipBits (bits : Fin 3 → Bool) : Fin 3 → Bool := fun i => !(bits i)
lemma chartFlipBits_orientation (bits : Fin 3 → Bool) (i : Fin 3) :
    (if chartFlipBits bits i then (-1 : ℝ) else 1) = -eps bits i := by
  unfold chartFlipBits eps
  cases bits i <;> norm_num
lemma chartFlipBits_involutive (bits : Fin 3 → Bool) :
    chartFlipBits (chartFlipBits bits)=bits := by
  funext i
  exact Bool.not_not (bits i)

def time (p : Slice) : ℝ := p.val.1
def coeff (p : Slice) (i : Fin 5) (j : Fin 6) : ℝ := p.val.2.W₂ i j
def output (p : Slice) (i : Fin 5) : ℝ := p.val.2.w₃ i

@[continuity] lemma continuous_time : Continuous time :=
  continuous_fst.comp continuous_subtype_val
@[continuity] lemma continuous_coeff (i : Fin 5) (j : Fin 6) :
    Continuous (fun p : Slice => coeff p i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp
    (continuous_W₂.comp (continuous_snd.comp continuous_subtype_val)))
@[continuity] lemma continuous_output (i : Fin 5) :
    Continuous (fun p : Slice => output p i) :=
  (continuous_apply i).comp (continuous_w₃.comp (continuous_snd.comp continuous_subtype_val))

noncomputable def core (p : Slice) (e : Equiv.Perm (Fin 5)) : CoefficientSystem (Fin 3) where
  lU := 0; lV := 0; lW := 0; lT := 0
  out i := output p (e (Fin.castAdd 2 i))
  U i := coeff p (e (Fin.castAdd 2 i)) 0
  V i := coeff p (e (Fin.castAdd 2 i)) 1
  W i := coeff p (e (Fin.castAdd 2 i)) 2
  T i := coeff p (e (Fin.castAdd 2 i)) 3

/-- The fixed unit orientation removes all divisions in the closed tests. -/
noncomputable def normalizedCoeff (l : Label) (p : Slice) (i : Fin 3) (j : Fin 6) : ℝ :=
  -eps (orientations l) i * coeff p (rowOrder l (Fin.castAdd 2 i)) j
noncomputable def hValue (l : Label) (p : Slice) : ℝ := normalizedCoeff l p 0 1
noncomputable def kValue (l : Label) (p : Slice) : ℝ := normalizedCoeff l p 1 0
noncomputable def nValue (l : Label) (p : Slice) : ℝ :=
  normalizedCoeff l p 2 0+(1-time p)*normalizedCoeff l p 2 3
noncomputable def mValue (l : Label) (p : Slice) : ℝ := normalizedCoeff l p 2 1
noncomputable def lValue (l : Label) (p : Slice) : ℝ := time p*normalizedCoeff l p 2 3

lemma continuous_normalizedCoeff (l : Label) (i : Fin 3) (j : Fin 6) :
    Continuous (fun p => normalizedCoeff l p i j) :=
  continuous_const.mul (continuous_coeff _ _)
lemma continuous_hValue (l : Label) : Continuous (hValue l) := continuous_normalizedCoeff l 0 1
lemma continuous_kValue (l : Label) : Continuous (kValue l) := continuous_normalizedCoeff l 1 0
lemma continuous_nValue (l : Label) : Continuous (nValue l) :=
  (continuous_normalizedCoeff l 2 0).add
    ((continuous_const.sub continuous_time).mul (continuous_normalizedCoeff l 2 3))
lemma continuous_mValue (l : Label) : Continuous (mValue l) := continuous_normalizedCoeff l 2 1
lemma continuous_lValue (l : Label) : Continuous (lValue l) :=
  continuous_time.mul (continuous_normalizedCoeff l 2 3)

noncomputable def intercept (p : Slice) (i : Fin 5) (x : InvariantState) : ℝ :=
  readout (time p) (coeff p i 0) (coeff p i 1) (coeff p i 2) (coeff p i 3) x
lemma continuous_intercept (i : Fin 5) (x : InvariantState) :
    Continuous (fun p : Slice => intercept p i x) := by
  unfold intercept readout starLinearForm
  exact ((((continuous_coeff i 0).mul continuous_const).add
    ((continuous_coeff i 1).mul continuous_const)).add
    ((continuous_coeff i 2).mul continuous_const)).add
    ((continuous_coeff i 3).mul (continuous_const.max
      (continuous_const.add (continuous_time.mul continuous_const))))

noncomputable def outputPattern : Fin 5 → ℝ := ![1,1,-1,1,-1]
def outputClass (l : Label) : Set Slice :=
  {p | ∀ i, output p (rowOrder l i)=outputPattern i}
def stationaryClass (l : Label) : Set Slice :=
  {p | ∀ i : Fin 3, coeff p (rowOrder l (Fin.castAdd 2 i)) 4=0 ∧
    coeff p (rowOrder l (Fin.castAdd 2 i)) 5=0}
def orientationClass (l : Label) : Set Slice :=
  {p | ∀ i : Fin 3, (core p (rowOrder l)).W i=eps (orientations l) i}
def carrierClass (l : Label) : Set Slice :=
  {p | (core p (rowOrder l)).U 0+(core p (rowOrder l)).W 0+
      (core p (rowOrder l)).T 0=0 ∧
    (core p (rowOrder l)).W 0+time p*(core p (rowOrder l)).T 0=0 ∧
    (core p (rowOrder l)).T 1=0 ∧
    (core p (rowOrder l)).V 1+(core p (rowOrder l)).W 1=0}
def branchClass (l : Label) : Set Slice :=
  {p | if branch l then
    kValue l p=1 ∧ hValue l p≤-1 ∧ nValue l p=1 ∧
      mValue l p=1+hValue l p ∧ lValue l p=0
  else hValue l p=0 ∧ kValue l p≤0 ∧ nValue l p=kValue l p-1 ∧
    mValue l p=0 ∧ lValue l p=1}
def directionClass (l : Label) : Set Slice := carrierClass l ∩ branchClass l

def headClass (l : Label) : Set Slice :=
  {p | if signed l then
    ∀ x : InvariantState, intercept p (rowOrder l 3) x+intercept p (rowOrder l 4) x=0
  else ∀ x : InvariantState,
    0 ≤ intercept p (rowOrder l 3) x ∧ 0 ≤ intercept p (rowOrder l 4) x}
def physicalClass (l : Label) : Set Slice :=
  outputClass l ∩ stationaryClass l ∩ orientationClass l ∩ directionClass l ∩ headClass l

lemma isClosed_outputClass (l : Label) : IsClosed (outputClass l) := by
  unfold outputClass
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_output _) continuous_const
lemma isClosed_stationaryClass (l : Label) : IsClosed (stationaryClass l) := by
  unfold stationaryClass
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i =>
    (isClosed_eq (continuous_coeff _ _) continuous_const).inter
      (isClosed_eq (continuous_coeff _ _) continuous_const)
lemma isClosed_orientationClass (l : Label) : IsClosed (orientationClass l) := by
  unfold orientationClass
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_coeff _ _) continuous_const
lemma isClosed_carrierClass (l : Label) : IsClosed (carrierClass l) := by
  change IsClosed {p : Slice | coeff p (rowOrder l 0) 0+coeff p (rowOrder l 0) 2+
    coeff p (rowOrder l 0) 3=0 ∧
    coeff p (rowOrder l 0) 2+time p*coeff p (rowOrder l 0) 3=0 ∧
    coeff p (rowOrder l 1) 3=0 ∧
    coeff p (rowOrder l 1) 1+coeff p (rowOrder l 1) 2=0}
  repeat' apply IsClosed.inter
  · exact isClosed_eq (((continuous_coeff _ _).add (continuous_coeff _ _)).add
      (continuous_coeff _ _)) continuous_const
  · exact isClosed_eq ((continuous_coeff _ _).add
      (continuous_time.mul (continuous_coeff _ _))) continuous_const
  · exact isClosed_eq (continuous_coeff _ _) continuous_const
  · exact isClosed_eq ((continuous_coeff _ _).add (continuous_coeff _ _)) continuous_const
lemma isClosed_branchClass (l : Label) : IsClosed (branchClass l) := by
  unfold branchClass
  cases hb : branch l <;> simp only [hb] <;> simp
  · repeat' apply IsClosed.inter
    · exact isClosed_eq (continuous_hValue l) continuous_const
    · exact isClosed_le (continuous_kValue l) continuous_const
    · exact isClosed_eq (continuous_nValue l) ((continuous_kValue l).sub continuous_const)
    · exact isClosed_eq (continuous_mValue l) continuous_const
    · exact isClosed_eq (continuous_lValue l) continuous_const
  · repeat' apply IsClosed.inter
    · exact isClosed_eq (continuous_kValue l) continuous_const
    · exact isClosed_le (continuous_hValue l) continuous_const
    · exact isClosed_eq (continuous_nValue l) continuous_const
    · exact isClosed_eq (continuous_mValue l) (continuous_const.add (continuous_hValue l))
    · exact isClosed_eq (continuous_lValue l) continuous_const
lemma isClosed_directionClass (l : Label) : IsClosed (directionClass l) :=
  (isClosed_carrierClass l).inter (isClosed_branchClass l)
lemma isClosed_headClass (l : Label) : IsClosed (headClass l) := by
  unfold headClass
  cases hs : signed l
  · change IsClosed {p : Slice | ∀ x : InvariantState,
      0 ≤ intercept p (rowOrder l 3) x ∧ 0 ≤ intercept p (rowOrder l 4) x}
    rw [Set.setOf_forall]
    exact isClosed_iInter fun x =>
      (isClosed_le continuous_const (continuous_intercept _ x)).inter
        (isClosed_le continuous_const (continuous_intercept _ x))
  · change IsClosed {p : Slice | ∀ x : InvariantState,
      intercept p (rowOrder l 3) x+intercept p (rowOrder l 4) x=0}
    rw [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_eq
      ((continuous_intercept _ x).add (continuous_intercept _ x)) continuous_const

/-- Actual finite coefficient tests are closed, including the r=1 endpoint. -/
theorem isClosed_physicalClass (l : Label) : IsClosed (physicalClass l) :=
  ((((isClosed_outputClass l).inter (isClosed_stationaryClass l)).inter
    (isClosed_orientationClass l)).inter (isClosed_directionClass l)).inter
      (isClosed_headClass l)
#print axioms isClosed_physicalClass
end MaxCaterpillar.Fiber.Count65.ActualStarLabels
