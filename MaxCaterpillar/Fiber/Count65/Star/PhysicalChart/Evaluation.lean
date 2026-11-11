import MaxCaterpillar.Fiber.Count65.Star.HeadBundles
import MaxCaterpillar.Fiber.Star65.Construction

/-! # Actual physical evaluation of the star reconstruction chart

The chart keeps three core rows and two physical translation heads. The
coefficient rescaling is proved on every real input of the actual first-layer
dictionary, rather than imposed as a feature-space convention.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65

private lemma vec_five_three {α : Type*} (a b c d e : α) :
    (![a,b,c,d,e] : Fin 5→α) 3=d := rfl

private lemma vec_five_four {α : Type*} (a b c d e : α) :
    (![a,b,c,d,e] : Fin 5→α) 4=e := rfl

/-- Undo the positive invariant-coordinate input rescaling. -/
noncomputable def unscaleCoefficients (r : ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![c 0/r,c 1,c 2,c 3/r]

/-- Append the two translation coefficients to an actual physical row. -/
noncomputable def extendRow (c : Fin 4 → ℝ) (a b : ℝ) : Fin 6 → ℝ :=
  ![c 0,c 1,c 2,c 3,a,b]

/-- Input coordinates used by the common actual invariant function space. -/
noncomputable def invariantState (r : ℝ) (x : Point 4) : InvariantState :=
  ((x 0-x 1)/r,x 1-x 2,x 3-x 2)

/-- The actual star features implement exactly the inverse coefficient change. -/
theorem unscaleCoefficients_readout {r : ℝ} (hr : 0<r) (c : Fin 4→ℝ)
    (q v w : ℝ) :
    starLinearForm r (unscaleCoefficients r c 0) (unscaleCoefficients r c 1)
      (unscaleCoefficients r c 2) (unscaleCoefficients r c 3) q v w =
    (coefficientReadout 1 c : InvariantState→ℝ) (q/r,v,w) := by
  have hq : relu q=r*relu (q/r) := by
    have h := relu_mul_pos hr (q/r)
    rw [mul_div_cancel' q (ne_of_gt hr)] at h
    exact h
  have ht : relu (q+r*v)=r*relu (q/r+v) := by
    have h := relu_mul_pos hr (q/r+v)
    have he : r*(q/r+v)=q+r*v := by field_simp [ne_of_gt hr]; ring
    rw [he] at h
    exact h
  change (c 0/r)*relu q+c 1*relu v+c 2*relu w+(c 3/r)*relu (q+r*v)=
    c 0*relu (q/r)+c 1*relu v+c 2*relu w+c 3*relu (q/r+1*v)
  rw [hq,ht,one_mul]
  field_simp [ne_of_gt hr]
  ring

/-- Three invariant core rows followed by two ordinary physical heads. -/
noncomputable def headLift (r : ℝ) (P Q N : Fin 4→ℝ)
    (h : HeadTopology.Data (featureSpace 1)) : Network 4 6 5 where
  W₁ := firstRows r
  b₁ := 0
  W₂ := ![extendRow (unscaleCoefficients r P) 0 0,
    extendRow (unscaleCoefficients r Q) 0 0,
    extendRow (unscaleCoefficients r N) 0 0,
    extendRow (unscaleCoefficients r (recoverReadout 1 h.2.1)) (h.1 0) (h.1 1),
    extendRow (unscaleCoefficients r (recoverReadout 1 h.2.2)) (h.1 2) (h.1 3)]
  b₂ := 0
  w₃ := ![1,1,-1,1,-1]
  b₃ := 0

theorem headLift_hasZeroBiases (r : ℝ) (P Q N : Fin 4→ℝ)
    (h : HeadTopology.Data (featureSpace 1)) : (headLift r P Q N h).HasZeroBiases :=
  ⟨rfl,rfl,rfl⟩

lemma extendRow_eval (r : ℝ) (c : Fin 4→ℝ) (a b : ℝ) (x : Point 4) :
    (∑ j,extendRow c a b j*firstValues r x j)=
      featureLin c r (x 0-x 1) (x 1-x 2) (x 3-x 2)+
        a*relu (x 2)+b*relu (-x 2) := by
  norm_num [Fin.sum_univ_succ,extendRow,firstValues,featureLin]
  ring

lemma extendUnscaledRow_eval {r : ℝ} (hr : 0<r) (c : Fin 4→ℝ)
    (a b : ℝ) (x : Point 4) :
    (∑ j,extendRow (unscaleCoefficients r c) a b j*firstValues r x j)=
      (coefficientReadout 1 c : InvariantState→ℝ) (invariantState r x)+
        a*relu (x 2)+b*relu (-x 2) := by
  rw [extendRow_eval]
  have he := unscaleCoefficients_readout hr c (x 0-x 1) (x 1-x 2) (x 3-x 2)
  change featureLin (unscaleCoefficients r c) r (x 0-x 1) (x 1-x 2) (x 3-x 2)=
    (coefficientReadout 1 c : InvariantState→ℝ) (invariantState r x) at he
  rw [he]

/-- Full all-input evaluation of the six-array physical chart network. -/
theorem headLift_eval {r : ℝ} (hr : 0<r) (P Q N : Fin 4→ℝ)
    (h : HeadTopology.Data (featureSpace 1)) (x : Point 4) :
    (headLift r P Q N h).eval x=
      (HeadTopology.toHeads h).eval (invariantState r x) (x 2)+
      relu ((coefficientReadout 1 P : InvariantState→ℝ) (invariantState r x))+
      relu ((coefficientReadout 1 Q : InvariantState→ℝ) (invariantState r x))-
      relu ((coefficientReadout 1 N : InvariantState→ℝ) (invariantState r x)) := by
  simp only [Network.eval,headLift,Pi.zero_apply,add_zero]
  simp_rw [firstRows_eval]
  rw [Fin.sum_univ_five]
  simp only [Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,one_mul,neg_mul,
    zero_mul,add_zero,zero_add]
  simp only [vec_five_three,vec_five_four,one_mul,neg_mul]
  change relu (∑ j,extendRow (unscaleCoefficients r P) 0 0 j*firstValues r x j)+
    relu (∑ j,extendRow (unscaleCoefficients r Q) 0 0 j*firstValues r x j)+
    (-relu (∑ j,extendRow (unscaleCoefficients r N) 0 0 j*firstValues r x j))+
    relu (∑ j,extendRow (unscaleCoefficients r (recoverReadout 1 h.2.1))
      (h.1 0) (h.1 1) j*firstValues r x j)+
    (-relu (∑ j,extendRow (unscaleCoefficients r (recoverReadout 1 h.2.2))
      (h.1 2) (h.1 3) j*firstValues r x j))=_
  rw [extendUnscaledRow_eval hr P,extendUnscaledRow_eval hr Q,extendUnscaledRow_eval hr N,
    extendUnscaledRow_eval hr (recoverReadout 1 h.2.1),
    extendUnscaledRow_eval hr (recoverReadout 1 h.2.2)]
  have hA := congrArg (fun f : featureSpace 1 => (f : InvariantState→ℝ) (invariantState r x))
    (coefficientReadout_recover (by norm_num : (0:ℝ)<1) h.2.1)
  have hB := congrArg (fun f : featureSpace 1 => (f : InvariantState→ℝ) (invariantState r x))
    (coefficientReadout_recover (by norm_num : (0:ℝ)<1) h.2.2)
  dsimp only at hA hB
  rw [hA,hB]
  simp only [zero_mul,add_zero]
  dsimp only [HeadTopology.toHeads,Mixed65.Heads.eval]
  simp only [add_assoc,add_left_comm,add_comm] <;> ring
/-- The inverse coordinate scaling varies continuously throughout r>0. -/
theorem continuous_unscaleCoefficients {β : Type*} [TopologicalSpace β]
    (r : β→ℝ) (c : β→Fin 4→ℝ) (hr : Continuous r) (hc : Continuous c)
    (hpos : ∀ b,0<r b) :
    Continuous (fun b => unscaleCoefficients (r b) (c b)) := by
  apply continuous_pi
  intro n
  fin_cases n
  · change Continuous (fun b => c b 0/r b)
    exact ((continuous_apply 0).comp hc).div hr (fun b => ne_of_gt (hpos b))
  · change Continuous (fun b => c b 1)
    exact (continuous_apply 1).comp hc
  · change Continuous (fun b => c b 2)
    exact (continuous_apply 2).comp hc
  · change Continuous (fun b => c b 3/r b)
    exact ((continuous_apply 3).comp hc).div hr (fun b => ne_of_gt (hpos b))

lemma continuous_extendRow {β : Type*} [TopologicalSpace β]
    (c : β→Fin 4→ℝ) (a b : β→ℝ) (hc : Continuous c) (ha : Continuous a)
    (hb : Continuous b) : Continuous (fun x => extendRow (c x) (a x) (b x)) := by
  apply continuous_pi
  intro n
  fin_cases n
  · change Continuous (fun x => c x 0)
    exact (continuous_apply 0).comp hc
  · change Continuous (fun x => c x 1)
    exact (continuous_apply 1).comp hc
  · change Continuous (fun x => c x 2)
    exact (continuous_apply 2).comp hc
  · change Continuous (fun x => c x 3)
    exact (continuous_apply 3).comp hc
  · change Continuous a
    exact ha
  · change Continuous b
    exact hb

lemma continuous_firstRows {β : Type*} [TopologicalSpace β]
    (r : β→ℝ) (hr : Continuous r) : Continuous (fun b => firstRows (r b)) := by
  apply continuous_pi
  intro i
  fin_cases i
  all_goals apply continuous_pi
  all_goals intro j
  all_goals fin_cases j
  all_goals first | exact continuous_const | exact hr | exact hr.neg |
    exact hr.sub continuous_const

/-- The actual physical chart is continuous in all real coefficients and in
its positive dictionary parameter, with the ordinary six-array network topology. -/
theorem continuous_headLift {β : Type*} [TopologicalSpace β]
    (r : β→ℝ) (P Q N : β→Fin 4→ℝ)
    (h : β→HeadTopology.Data (featureSpace 1))
    (hr : Continuous r) (hP : Continuous P) (hQ : Continuous Q) (hN : Continuous N)
    (hh : Continuous h) (hpos : ∀ b,0<r b) :
    Continuous (fun b => headLift (r b) (P b) (Q b) (N b) (h b)) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_firstRows r hr,continuous_const,?_,continuous_const,
    continuous_const,continuous_const⟩
  have huP := continuous_unscaleCoefficients r P hr hP hpos
  have huQ := continuous_unscaleCoefficients r Q hr hQ hpos
  have huN := continuous_unscaleCoefficients r N hr hN hpos
  have hA := (continuous_recoverReadout 1).comp hh.snd.fst
  have hB := (continuous_recoverReadout 1).comp hh.snd.snd
  have huA := continuous_unscaleCoefficients r (fun b => recoverReadout 1 (h b).2.1)
    hr hA hpos
  have huB := continuous_unscaleCoefficients r (fun b => recoverReadout 1 (h b).2.2)
    hr hB hpos
  have hs (i : Fin 4) : Continuous (fun b => (h b).1 i) :=
    (continuous_apply i).comp hh.fst
  have hp := continuous_extendRow _ (fun _ => 0) (fun _ => 0) huP continuous_const continuous_const
  have hq := continuous_extendRow _ (fun _ => 0) (fun _ => 0) huQ continuous_const continuous_const
  have hn := continuous_extendRow _ (fun _ => 0) (fun _ => 0) huN continuous_const continuous_const
  have ha := continuous_extendRow _ _ _ huA (hs 0) (hs 1)
  have hb := continuous_extendRow _ _ _ huB (hs 2) (hs 3)
  apply continuous_pi
  intro k
  fin_cases k
  · exact hp
  · exact hq
  · exact hn
  · exact ha
  · exact hb
end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
