import MaxCaterpillar.Fiber.Count65.Mixed.PhysicalNormalForm
import MaxCaterpillar.Fiber.Count65.Topology

/-! # Closed finite classes of actual normalized mixed physical networks

All class tests below are equations or weak inequalities in original physical
coefficients and actual all-real head readouts. No normal-form choice, data
sample, or topology assumption enters the definition of a class.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Fiber.Count65.ActualMixedLabels
open Set Function Mixed65 MaxCaterpillar.Frontier

abbrev Slice := {p : ℝ × Network 4 6 5 //
  0 < p.1 ∧ p.2.W₁=firstRows p.1 ∧
    (∀ x, p.2.eval x=Maximum 4 x) ∧ (∀ i,p.2.w₃ i=1 ∨ p.2.w₃ i = -1)}

abbrev Label := Equiv.Perm (Fin 5) × NonpairedLabel

def rowOrder (l : Label) := l.1
def branch (l : Label) := l.2.1
def orientations (l : Label) := l.2.2.1
def signed (l : Label) := l.2.2.2
noncomputable def eps (bits : Fin 3 → Bool) (i : Fin 3) : ℝ := if bits i then -1 else 1

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

noncomputable def core (p : Slice) (e : Equiv.Perm (Fin 5)) : ResidualSystem (Fin 3) where
  lU := 0; lV := 0; lW := 0; lT := 0
  out i := output p (e (Fin.castAdd 2 i))
  U i := coeff p (e (Fin.castAdd 2 i)) 0
  V i := coeff p (e (Fin.castAdd 2 i)) 1
  W i := coeff p (e (Fin.castAdd 2 i)) 2
  T i := coeff p (e (Fin.castAdd 2 i)) 3

noncomputable def parameter (l : Label) (p : Slice) : ℝ :=
  if branch l then eps (orientations l) 0 * coeff p (rowOrder l 0) 1
  else eps (orientations l) 1 * coeff p (rowOrder l 1) 3

@[continuity] lemma continuous_parameter (l : Label) : Continuous (parameter l) := by
  unfold parameter
  cases hb : branch l <;> simp [hb]
  all_goals exact continuous_const.mul (continuous_coeff _ _)

noncomputable def intercept (p : Slice) (i : Fin 5) (x : InvariantState) : ℝ :=
  readout (time p) (coeff p i 0) (coeff p i 1) (coeff p i 2) (coeff p i 3) x

lemma continuous_intercept (i : Fin 5) (x : InvariantState) :
    Continuous (fun p : Slice => intercept p i x) := by
  unfold intercept readout form relu
  exact ((((continuous_coeff i 0).mul continuous_const).add
    ((continuous_coeff i 1).mul continuous_const)).add
    ((continuous_coeff i 2).mul continuous_const)).add
    ((continuous_coeff i 3).mul (continuous_const.max
      ((continuous_time.mul continuous_const).sub continuous_const)))

noncomputable def outputPattern : Fin 5 → ℝ := ![1,1,-1,1,-1]

def outputClass (l : Label) : Set Slice :=
  {p | ∀ i, output p (rowOrder l i)=outputPattern i}
def stationaryClass (l : Label) : Set Slice :=
  {p | ∀ i : Fin 3, coeff p (rowOrder l (Fin.castAdd 2 i)) 4=0 ∧
    coeff p (rowOrder l (Fin.castAdd 2 i)) 5=0}
def orientationClass (l : Label) : Set Slice :=
  {p | ∀ i : Fin 3, (core p (rowOrder l)).W i=eps (orientations l) i}
def directionClass (l : Label) : Set Slice :=
  {p | if branch l then
    1+time p ≤ time p*parameter l p ∧
      (core p (rowOrder l)).HasBDirections (time p) (parameter l p)
  else 1 ≤ time p*parameter l p ∧
      (core p (rowOrder l)).HasADirections (time p) (parameter l p)}
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

lemma isClosed_directionClass (l : Label) : IsClosed (directionClass l) := by
  have ht := continuous_time
  have hp := continuous_parameter l
  have hU (i : Fin 3) := continuous_coeff (rowOrder l (Fin.castAdd 2 i)) 0
  have hV (i : Fin 3) := continuous_coeff (rowOrder l (Fin.castAdd 2 i)) 1
  have hW (i : Fin 3) := continuous_coeff (rowOrder l (Fin.castAdd 2 i)) 2
  have hT (i : Fin 3) := continuous_coeff (rowOrder l (Fin.castAdd 2 i)) 3
  unfold directionClass
  cases hb : branch l <;> simp only [hb] <;> simp
  · simp only [ResidualSystem.HasADirections,core]
    repeat' apply IsClosed.inter
    · exact isClosed_le continuous_const (ht.mul hp)
    · exact isClosed_eq (hU 0) ((continuous_const.add ht).neg.mul (hW 0))
    · exact isClosed_eq (hV 0) continuous_const
    · exact isClosed_eq (hT 0) (hW 0)
    · exact isClosed_eq (hU 1) (hW 1).neg
    · exact isClosed_eq (hV 1) (hW 1).neg
    · exact isClosed_eq (hT 1) (hp.mul (hW 1))
    · exact isClosed_eq (hU 2) ((continuous_const.add ht).neg.mul (hW 2))
    · exact isClosed_eq (hV 2) continuous_const
    · exact isClosed_eq (hT 2) ((hp.add continuous_const).mul (hW 2))
  · simp only [ResidualSystem.HasBDirections,core]
    repeat' apply IsClosed.inter
    · exact isClosed_le (continuous_const.add ht) (ht.mul hp)
    · exact isClosed_eq (hU 0) ((continuous_const.add ht).neg.mul (hW 0))
    · exact isClosed_eq (hV 0) (hp.mul (hW 0))
    · exact isClosed_eq (hT 0) (hW 0)
    · exact isClosed_eq (hU 1) (hW 1).neg
    · exact isClosed_eq (hV 1) (hW 1).neg
    · exact isClosed_eq (hT 1) continuous_const
    · exact isClosed_eq (hU 2) (hW 2).neg
    · exact isClosed_eq (hV 2) ((hp.sub continuous_const).mul (hW 2))
    · exact isClosed_eq (hT 2) continuous_const

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

/-- The finite physical label tests are closed in the full actual normalized
mixed first-row slice, with arbitrary original biases and incoming weights. -/
theorem isClosed_physicalClass (l : Label) : IsClosed (physicalClass l) :=
  ((((isClosed_outputClass l).inter (isClosed_stationaryClass l)).inter
    (isClosed_orientationClass l)).inter (isClosed_directionClass l)).inter
      (isClosed_headClass l)

#print axioms isClosed_physicalClass
end MaxCaterpillar.Fiber.Count65.ActualMixedLabels
