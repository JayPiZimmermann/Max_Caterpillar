import MaxCaterpillar.Fiber.Count65.Paired.PhysicalAtoms
import MaxCaterpillar.Fiber.Count65.Paired.Absorption

/-! # Safe folding for baselines with two oppositely signed increments

An arbitrary second-layer representation of `A*q-B*r+c*u+d*v`, with
`A,B>0`, admits a physical coefficient path to a representation of `Q-N`
on the full nonnegative quadrant. The paired code and all spectator gates
stay fixed. This reduction does not classify the remaining quadrant fiber.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineFold
open BigOperators Frontier Absorption

variable {m r : ℕ}

def features (q r u v : ℝ) : Fin 6 → ℝ :=
  ![q,r,relu u,relu (-u),relu v,relu (-v)]

def positiveAnchor (c d u v : ℝ) : ℝ :=
  relu c*relu u+relu (-c)*relu (-u)+relu d*relu v+relu (-d)*relu (-v)

def negativeAnchor (c d u v : ℝ) : ℝ :=
  relu (-c)*relu u+relu c*relu (-u)+relu (-d)*relu v+relu d*relu (-v)

lemma positiveAnchor_nonneg (c d u v : ℝ) : 0 ≤ positiveAnchor c d u v := by
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (relu_nonneg _) (relu_nonneg _))
    (mul_nonneg (relu_nonneg _) (relu_nonneg _)))
    (mul_nonneg (relu_nonneg _) (relu_nonneg _)))
    (mul_nonneg (relu_nonneg _) (relu_nonneg _))

lemma negativeAnchor_nonneg (c d u v : ℝ) : 0 ≤ negativeAnchor c d u v := by
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (relu_nonneg _) (relu_nonneg _))
    (mul_nonneg (relu_nonneg _) (relu_nonneg _)))
    (mul_nonneg (relu_nonneg _) (relu_nonneg _)))
    (mul_nonneg (relu_nonneg _) (relu_nonneg _))

lemma anchor_difference (c d u v : ℝ) :
    positiveAnchor c d u v-negativeAnchor c d u v=c*u+d*v := by
  have hc := relu_sub_relu_neg c
  have hd := relu_sub_relu_neg d
  have hu := relu_sub_relu_neg u
  have hv := relu_sub_relu_neg v
  dsimp [positiveAnchor,negativeAnchor]
  calc
    _ = (relu c-relu (-c))*(relu u-relu (-u))+
        (relu d-relu (-d))*(relu v-relu (-v)) := by ring
    _ = _ := by rw [hc,hd,hu,hv]

/-- Actual outgoing-row coefficients, without any restriction on the source row. -/
def foldRow (A B c d t : ℝ) (W : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![W 0,W 1,
    (1-t)*W 2+t*(W 0/A*relu c+W 1/B*relu (-c)),
    (1-t)*W 3+t*(W 0/A*relu (-c)+W 1/B*relu c),
    (1-t)*W 4+t*(W 0/A*relu d+W 1/B*relu (-d)),
    (1-t)*W 5+t*(W 0/A*relu (-d)+W 1/B*relu d)]

private lemma sum_six (f : Fin 6 → ℝ) :
    (∑ j, f j)=f 0+(f 1+(f 2+(f 3+(f 4+f 5)))) := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rfl

lemma relu_mul_nonneg (a u : ℝ) (ha : 0≤a) : relu (a*u)=a*relu u := by
  rcases eq_or_lt_of_le ha with h|h
  · rw [← h]; simp [relu]
  · exact relu_mul_pos h u

lemma dot_features (W : Fin 6 → ℝ) (q r u v : ℝ) :
    (∑ j, W j*features q r u v j)=
      W 0*q+W 1*r+W 2*relu u+W 3*relu (-u)+W 4*relu v+W 5*relu (-v) := by
  rw [sum_six]
  change W 0*q+(W 1*r+(W 2*relu u+(W 3*relu (-u)+
    (W 4*relu v+W 5*relu (-v)))))=_
  ring

/-- Row pullback is evaluated on a genuine point of the same feature domain. -/
theorem foldRow_dot (A B c d t : ℝ) (ht : t≤1) (W : Fin 6 → ℝ)
    (q r u v : ℝ) :
    (∑ j, foldRow A B c d t W j*features q r u v j)=
      ∑ j, W j*features (q+t/A*positiveAnchor c d u v)
        (r+t/B*negativeAnchor c d u v) ((1-t)*u) ((1-t)*v) j := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,foldRow,features,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
  change W 0*q+(W 1*r+(((1-t)*W 2+t*(W 0/A*relu c+W 1/B*relu (-c)))*relu u+
    (((1-t)*W 3+t*(W 0/A*relu (-c)+W 1/B*relu c))*relu (-u)+
    (((1-t)*W 4+t*(W 0/A*relu d+W 1/B*relu (-d)))*relu v+
      ((1-t)*W 5+t*(W 0/A*relu (-d)+W 1/B*relu d))*relu (-v)))))=
    W 0*(q+t/A*positiveAnchor c d u v)+(W 1*(r+t/B*negativeAnchor c d u v)+
      (W 2*relu ((1-t)*u)+(W 3*relu (-((1-t)*u))+
        (W 4*relu ((1-t)*v)+W 5*relu (-((1-t)*v))))))
  rw [show -((1-t)*u)=(1-t)*(-u) by ring,
    show -((1-t)*v)=(1-t)*(-v) by ring]
  simp only [relu_mul_nonneg (1-t) _ (sub_nonneg.mpr ht),
    positiveAnchor,negativeAnchor]
  ring

theorem fold_target (A B c d t q r u v : ℝ) (hA : A≠0) (hB : B≠0) :
    A*(q+t/A*positiveAnchor c d u v)-B*(r+t/B*negativeAnchor c d u v)+
      c*((1-t)*u)+d*((1-t)*v)=A*q-B*r+c*u+d*v := by
  have hd := anchor_difference c d u v
  field_simp [hA,hB]
  linear_combination A*B*t*hd

@[simp] theorem foldRow_zero (A B c d : ℝ) (W : Fin 6 → ℝ) :
    foldRow A B c d 0 W=W := by
  funext j
  fin_cases j <;> simp [foldRow] <;> rfl

theorem continuous_foldRow (A B c d : ℝ) (W : Fin 6 → ℝ) :
    Continuous (fun t : ℝ => foldRow A B c d t W) := by
  apply continuous_pi
  intro j
  fin_cases j <;> simp only [foldRow,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons] <;> continuity

/-- A full quadrant identity follows from an arbitrary source representation.
No crossing-group classification, nonzero-output premise, or code alignment
is assumed. Second-neuron biases and the output bias are retained. -/
theorem folded_quadrant_identity (A B c d : ℝ) (hA : 0<A) (hB : 0<B)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ q r u v : ℝ, 0≤q → 0≤r →
      (∑ k, weights k*relu ((∑ j, C k j*features q r u v j)+bias k))+θ=
        A*q-B*r+c*u+d*v)
    (Q N : ℝ) (hQ : 0≤Q) (hN : 0≤N) :
    (∑ k, weights k*relu (C k 0/A*Q+C k 1/B*N+bias k))+θ=Q-N := by
  have hh := hfit (Q/A) (N/B) 0 0 (div_nonneg hQ hA.le) (div_nonneg hN hB.le)
  have hdot : ∀ k, (∑ j, C k j*features (Q/A) (N/B) 0 0 j)=
      C k 0/A*Q+C k 1/B*N := by
    intro k
    simp [features,relu,Fin.sum_univ_succ]
    ring
  simp_rw [hdot] at hh
  rw [show A*(Q/A)=Q by field_simp [ne_of_gt hA]; ring,
    show B*(N/B)=N by field_simp [ne_of_gt hB]; ring] at hh
  simpa using hh

def code (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) (i : Fin 2) : ℝ :=
  U i 0*x 1+U i 1*x 3

def actualFeatures (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) : Fin 6 → ℝ :=
  features (relu (x 0-x 1)) (relu (x 2-x 3)) (code U x 0) (code U x 1)

theorem first_activation (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) (j : Fin 6) :
    relu (∑ i, pairedRows U j i*x i)=actualFeatures U x j := by
  fin_cases j <;> simp [pairedRows,actualFeatures,features,code,Fin.sum_univ_succ] <;>
    congr 1 <;> simp only [show (Fin.succ (2:Fin 3):Fin 4)=3 from rfl] <;> ring

def completion (U : Fin 2 → Fin 2 → ℝ) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ) : Network 4 6 m where
  W₁ := pairedRows U
  b₁ := 0
  W₂ := C
  b₂ := bias
  w₃ := weights
  b₃ := θ

theorem eq_completion_of_first (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hW : net.W₁=pairedRows U) (hb : net.b₁=0) :
    net=completion U net.W₂ net.b₂ net.w₃ net.b₃ := by
  cases net
  cases hW
  cases hb
  rfl

lemma completion_eval (U : Fin 2 → Fin 2 → ℝ) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ) (x : Point 4) :
    (completion U C bias weights θ).eval x=
      (∑ k, weights k*relu ((∑ j, C k j*actualFeatures U x j)+bias k))+θ := by
  simp only [Network.eval,completion,Pi.zero_apply,add_zero,first_activation]

def target (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ) (x : Point 4) : ℝ :=
  A*relu (x 0-x 1)-B*relu (x 2-x 3)+c*code U x 0+d*code U x 1

def targetRow (A B c d : ℝ) : Fin 6 → ℝ := ![A,-B,c,-c,d,-d]

lemma targetRow_dot (A B c d q r u v : ℝ) :
    (∑ j, targetRow A B c d j*features q r u v j)=A*q-B*r+c*u+d*v := by
  rw [dot_features]
  change A*q+(-B)*r+c*relu u+(-c)*relu (-u)+d*relu v+(-d)*relu (-v)=_
  linear_combination c*(relu_sub_relu_neg u)+d*(relu_sub_relu_neg v)

lemma targetRow_preact (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ) (x : Point 4) :
    preact (pairedRows U) 0 (targetRow A B c d) 0 x=target U A B c d x := by
  simp only [preact,Pi.zero_apply,add_zero,first_activation]
  exact targetRow_dot A B c d _ _ _ _

/-- A concrete signed-pair realization witnesses that the baseline-fit premise
is satisfiable for every code and every real target coefficient. -/
theorem signed_baseline_witness (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ) :
    ∃ C : Fin 3 → Fin 6 → ℝ, ∃ weights : Fin 3 → ℝ,
      ∀ x, (completion U C 0 weights 0).eval x=target U A B c d x := by
  refine ⟨![targetRow A B c d,fun j => -targetRow A B c d j,0],![1,-1,0],?_⟩
  intro x
  rw [completion_eval]
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Pi.zero_apply,
    add_zero,one_mul,neg_one_mul,zero_mul,zero_add]
  change relu (∑ j, targetRow A B c d j*actualFeatures U x j)-
    relu (∑ j, -targetRow A B c d j*actualFeatures U x j)=_
  simp only [neg_mul,Finset.sum_neg_distrib]
  rw [relu_sub_relu_neg]
  exact targetRow_dot A B c d _ _ _ _

/-- The transformed input only witnesses exactness; the actual first-layer
parameters never change during the coefficient homotopy. -/
def foldInput (U : Fin 2 → Fin 2 → ℝ) (A B c d t : ℝ) (x : Point 4) : Point 4 :=
  ![(1-t)*x 1+relu (x 0-x 1)+t/A*positiveAnchor c d (code U x 0) (code U x 1),
    (1-t)*x 1,
    (1-t)*x 3+relu (x 2-x 3)+t/B*negativeAnchor c d (code U x 0) (code U x 1),
    (1-t)*x 3]

lemma code_foldInput (U : Fin 2 → Fin 2 → ℝ) (A B c d t : ℝ)
    (x : Point 4) (i : Fin 2) :
    code U (foldInput U A B c d t x) i=(1-t)*code U x i := by
  change U i 0*((1-t)*x 1)+U i 1*((1-t)*x 3)=
    (1-t)*(U i 0*x 1+U i 1*x 3)
  ring

theorem actualFeatures_foldInput (U : Fin 2 → Fin 2 → ℝ)
    (A B c d t : ℝ) (hA : 0<A) (hB : 0<B) (ht : 0≤t) (x : Point 4) :
    actualFeatures U (foldInput U A B c d t x)=
      features (relu (x 0-x 1)+t/A*positiveAnchor c d (code U x 0) (code U x 1))
        (relu (x 2-x 3)+t/B*negativeAnchor c d (code U x 0) (code U x 1))
        ((1-t)*code U x 0) ((1-t)*code U x 1) := by
  unfold actualFeatures
  rw [code_foldInput,code_foldInput]
  have hq : (foldInput U A B c d t x) 0-(foldInput U A B c d t x) 1=
      relu (x 0-x 1)+t/A*positiveAnchor c d (code U x 0) (code U x 1) := by
    change (1-t)*x 1+relu (x 0-x 1)+t/A*positiveAnchor c d (code U x 0) (code U x 1)-
      (1-t)*x 1=_
    ring
  have hr : (foldInput U A B c d t x) 2-(foldInput U A B c d t x) 3=
      relu (x 2-x 3)+t/B*negativeAnchor c d (code U x 0) (code U x 1) := by
    change (1-t)*x 3+relu (x 2-x 3)+t/B*negativeAnchor c d (code U x 0) (code U x 1)-
      (1-t)*x 3=_
    ring
  rw [hq,hr,relu_of_nonneg (add_nonneg (relu_nonneg _)
    (mul_nonneg (div_nonneg ht hA.le) (positiveAnchor_nonneg _ _ _ _))),
    relu_of_nonneg (add_nonneg (relu_nonneg _)
    (mul_nonneg (div_nonneg ht hB.le) (negativeAnchor_nonneg _ _ _ _)))]

theorem target_foldInput (U : Fin 2 → Fin 2 → ℝ)
    (A B c d t : ℝ) (hA : 0<A) (hB : 0<B) (ht : 0≤t) (x : Point 4) :
    target U A B c d (foldInput U A B c d t x)=target U A B c d x := by
  have hh := actualFeatures_foldInput U A B c d t hA hB ht x
  have hq := congrFun hh 0
  have hr := congrFun hh 1
  change relu ((foldInput U A B c d t x) 0-(foldInput U A B c d t x) 1)=_ at hq
  change relu ((foldInput U A B c d t x) 2-(foldInput U A B c d t x) 3)=_ at hr
  unfold target
  rw [hq,hr,code_foldInput,code_foldInput]
  exact fold_target A B c d t _ _ _ _ (ne_of_gt hA) (ne_of_gt hB)

def foldedCompletion (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ t : ℝ) : Network 4 6 m :=
  completion U (fun k => foldRow A B c d t (C k)) bias weights θ

@[simp] theorem foldedCompletion_zero (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ) :
    foldedCompletion U A B c d C bias weights θ 0=completion U C bias weights θ := by
  simp only [foldedCompletion,foldRow_zero]

theorem foldedCompletion_eval (U : Fin 2 → Fin 2 → ℝ)
    (A B c d t : ℝ) (hA : 0<A) (hB : 0<B) (ht0 : 0≤t) (ht1 : t≤1)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ) (x : Point 4) :
    (foldedCompletion U A B c d C bias weights θ t).eval x=
      (completion U C bias weights θ).eval (foldInput U A B c d t x) := by
  simp only [foldedCompletion,completion_eval,actualFeatures_foldInput U A B c d t hA hB ht0]
  simp only [actualFeatures,foldRow_dot A B c d t ht1]

theorem foldedCompletion_preserves (U : Fin 2 → Fin 2 → ℝ)
    (A B c d t : ℝ) (hA : 0<A) (hB : 0<B) (ht0 : 0≤t) (ht1 : t≤1)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=target U A B c d x)
    (x : Point 4) :
    (foldedCompletion U A B c d C bias weights θ t).eval x=target U A B c d x := by
  rw [foldedCompletion_eval U A B c d t hA hB ht0 ht1,hfit,
    target_foldInput U A B c d t hA hB ht0]

/-- The same path also handles the reversed increment signs by taking `ε=-1`. -/
theorem foldedCompletion_preserves_smul (U : Fin 2 → Fin 2 → ℝ)
    (A B c d ε t : ℝ) (hA : 0<A) (hB : 0<B) (ht0 : 0≤t) (ht1 : t≤1)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=ε*target U A B c d x)
    (x : Point 4) :
    (foldedCompletion U A B c d C bias weights θ t).eval x=ε*target U A B c d x := by
  rw [foldedCompletion_eval U A B c d t hA hB ht0 ht1,hfit,
    target_foldInput U A B c d t hA hB ht0]

theorem continuous_foldedCompletion (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ) :
    Continuous (foldedCompletion U A B c d C bias weights θ) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,continuous_const,continuous_const,continuous_const⟩
  apply continuous_pi
  intro k
  exact continuous_foldRow A B c d (C k)

def positiveCoordinate (U : Fin 2 → Fin 2 → ℝ) (A c d : ℝ) (x : Point 4) : ℝ :=
  A*relu (x 0-x 1)+positiveAnchor c d (code U x 0) (code U x 1)

def negativeCoordinate (U : Fin 2 → Fin 2 → ℝ) (B c d : ℝ) (x : Point 4) : ℝ :=
  B*relu (x 2-x 3)+negativeAnchor c d (code U x 0) (code U x 1)

/-- Every endpoint preactivation factors through these same two coordinates. -/
theorem foldRow_endpoint (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (hA : A≠0) (hB : B≠0) (W : Fin 6 → ℝ) (x : Point 4) :
    (∑ j, foldRow A B c d 1 W j*actualFeatures U x j)=
      W 0/A*positiveCoordinate U A c d x+W 1/B*negativeCoordinate U B c d x := by
  unfold actualFeatures
  rw [foldRow_dot A B c d 1 le_rfl,dot_features]
  simp only [sub_self,zero_mul,neg_zero,show relu 0=0 from relu_of_nonneg le_rfl,mul_zero,add_zero]
  dsimp [positiveCoordinate,negativeCoordinate]
  field_simp [hA,hB]
  ring

theorem foldedCompletion_endpoint (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (hA : A≠0) (hB : B≠0) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ) (x : Point 4) :
    (foldedCompletion U A B c d C bias weights θ 1).eval x=
      (∑ k, weights k*relu (C k 0/A*positiveCoordinate U A c d x+
        C k 1/B*negativeCoordinate U B c d x+bias k))+θ := by
  simp only [foldedCompletion,completion_eval,foldRow_endpoint U A B c d hA hB]

/-- Both endpoint coordinates are nonnegative on all actual inputs. -/
theorem coordinates_nonneg (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (hA : 0≤A) (hB : 0≤B) (x : Point 4) :
    0≤positiveCoordinate U A c d x ∧ 0≤negativeCoordinate U B c d x :=
  ⟨add_nonneg (mul_nonneg hA (relu_nonneg _)) (positiveAnchor_nonneg _ _ _ _),
    add_nonneg (mul_nonneg hB (relu_nonneg _)) (negativeAnchor_nonneg _ _ _ _)⟩

/-- Conversely, every point of the quadrant is realized, including its boundary. -/
theorem coordinates_surjective (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (hA : 0<A) (hB : 0<B) (Q N : ℝ) (hQ : 0≤Q) (hN : 0≤N) :
    ∃ x : Point 4, positiveCoordinate U A c d x=Q ∧ negativeCoordinate U B c d x=N := by
  refine ⟨![Q/A,0,N/B,0],?_,?_⟩
  · change A*relu (Q/A-0)+positiveAnchor c d (U 0 0*0+U 0 1*0)
        (U 1 0*0+U 1 1*0)=Q
    simp [positiveAnchor,relu_of_nonneg (div_nonneg hQ hA.le),relu]
    field_simp [ne_of_gt hA]
    ring
  · change B*relu (N/B-0)+negativeAnchor c d (U 0 0*0+U 0 1*0)
        (U 1 0*0+U 1 1*0)=N
    simp [negativeAnchor,relu_of_nonneg (div_nonneg hN hB.le),relu]
    field_simp [ne_of_gt hB]
    ring

theorem target_coordinates (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ) (x : Point 4) :
    target U A B c d x=positiveCoordinate U A c d x-negativeCoordinate U B c d x := by
  dsimp [target,positiveCoordinate,negativeCoordinate]
  linarith only [anchor_difference c d (code U x 0) (code U x 1)]

/-- This is the attachment interface for a general quadrant-fiber theorem:
the physical source identity gives an unrestricted quadrant fit at the endpoint. -/
theorem physical_quadrant_identity (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (hA : 0<A) (hB : 0<B) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=target U A B c d x)
    (Q N : ℝ) (hQ : 0≤Q) (hN : 0≤N) :
    (∑ k, weights k*relu (C k 0/A*Q+C k 1/B*N+bias k))+θ=Q-N := by
  obtain ⟨x,hxQ,hxN⟩ := coordinates_surjective U A B c d hA hB Q N hQ hN
  have hh := foldedCompletion_preserves U A B c d 1 hA hB (by norm_num) le_rfl
    C bias weights θ hfit x
  rw [foldedCompletion_endpoint U A B c d (ne_of_gt hA) (ne_of_gt hB),
    target_coordinates,hxQ,hxN] at hh
  exact hh

theorem physical_quadrant_identity_smul (U : Fin 2 → Fin 2 → ℝ) (A B c d ε : ℝ)
    (hA : 0<A) (hB : 0<B) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=ε*target U A B c d x)
    (Q N : ℝ) (hQ : 0≤Q) (hN : 0≤N) :
    (∑ k, weights k*relu (C k 0/A*Q+C k 1/B*N+bias k))+θ=ε*(Q-N) := by
  obtain ⟨x,hxQ,hxN⟩ := coordinates_surjective U A B c d hA hB Q N hQ hN
  have hh := foldedCompletion_preserves_smul U A B c d ε 1 hA hB (by norm_num) le_rfl
    C bias weights θ hfit x
  rw [foldedCompletion_endpoint U A B c d (ne_of_gt hA) (ne_of_gt hB),
    target_coordinates,hxQ,hxN] at hh
  exact hh

def withSpectators (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ) (t : ℝ) : Network 4 6 (m+r) :=
  appendSpectators (foldedCompletion U A B c d C bias weights θ t) rows sbias sweights

theorem withSpectators_preserves (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (hA : 0<A) (hB : 0<B) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=target U A B c d x)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) (x : Point 4) :
    (withSpectators U A B c d C bias weights θ rows sbias sweights t).eval x=
      (withSpectators U A B c d C bias weights θ rows sbias sweights 0).eval x := by
  simp only [withSpectators,appendSpectators_eval]
  rw [foldedCompletion_preserves U A B c d t hA hB ht0 ht1 C bias weights θ hfit,
    foldedCompletion_preserves U A B c d 0 hA hB (by norm_num) (by norm_num)
      C bias weights θ hfit]
  rfl

/-- A path in the ordinary, all-input exact network fiber. The first layer and
every spectator coefficient are unchanged, even when spectators have kinks. -/
theorem withSpectators_joinedIn_exact (U : Fin 2 → Fin 2 → ℝ) (A B c d : ℝ)
    (hA : 0<A) (hB : 0<B) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=target U A B c d x)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x,
      (withSpectators U A B c d C bias weights θ rows sbias sweights 0).eval x=Maximum 4 x) :
    JoinedIn (ExactSet 4 6 (m+r))
      (withSpectators U A B c d C bias weights θ rows sbias sweights 0)
      (withSpectators U A B c d C bias weights θ rows sbias sweights 1) := by
  have hc := continuous_appendSpectators (foldedCompletion U A B c d C bias weights θ)
    (continuous_foldedCompletion U A B c d C bias weights θ) rows sbias sweights
  apply JoinedIn.ofLine hc.continuousOn rfl rfl
  rintro _ ⟨t,ht,rfl⟩ x
  change (withSpectators U A B c d C bias weights θ rows sbias sweights t).eval x=Maximum 4 x
  rw [withSpectators_preserves U A B c d hA hB C bias weights θ hfit rows sbias sweights
    t ht.1 ht.2 x]
  exact hsource x

theorem withSpectators_smul_preserves (U : Fin 2 → Fin 2 → ℝ) (A B c d ε : ℝ)
    (hA : 0<A) (hB : 0<B) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=ε*target U A B c d x)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) (x : Point 4) :
    (withSpectators U A B c d C bias weights θ rows sbias sweights t).eval x=
      (withSpectators U A B c d C bias weights θ rows sbias sweights 0).eval x := by
  simp only [withSpectators,appendSpectators_eval]
  rw [foldedCompletion_preserves_smul U A B c d ε t hA hB ht0 ht1 C bias weights θ hfit,
    foldedCompletion_preserves_smul U A B c d ε 0 hA hB (by norm_num) (by norm_num)
      C bias weights θ hfit]
  rfl

theorem withSpectators_smul_joinedIn_exact (U : Fin 2 → Fin 2 → ℝ) (A B c d ε : ℝ)
    (hA : 0<A) (hB : 0<B) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=ε*target U A B c d x)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x,
      (withSpectators U A B c d C bias weights θ rows sbias sweights 0).eval x=Maximum 4 x) :
    JoinedIn (ExactSet 4 6 (m+r))
      (withSpectators U A B c d C bias weights θ rows sbias sweights 0)
      (withSpectators U A B c d C bias weights θ rows sbias sweights 1) := by
  have hc := continuous_appendSpectators (foldedCompletion U A B c d C bias weights θ)
    (continuous_foldedCompletion U A B c d C bias weights θ) rows sbias sweights
  apply JoinedIn.ofLine hc.continuousOn rfl rfl
  rintro _ ⟨t,ht,rfl⟩ x
  change (withSpectators U A B c d C bias weights θ rows sbias sweights t).eval x=Maximum 4 x
  rw [withSpectators_smul_preserves U A B c d ε hA hB C bias weights θ hfit rows sbias sweights
    t ht.1 ht.2 x]
  exact hsource x

end MaxCaterpillar.Fiber.Count65.Paired.BaselineFold
