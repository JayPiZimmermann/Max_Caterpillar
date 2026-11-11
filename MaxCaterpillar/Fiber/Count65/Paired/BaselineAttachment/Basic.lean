import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.Attachment
import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.SignedSplit
import MaxCaterpillar.Fiber.Count65.Paired.SecondReindex

/-! Literal baseline networks and elementary physical cleanup paths. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
open BigOperators Absorption QuadrantGroups
variable {N m k : ℕ}

def readout (a : Network N m k) (S : Finset (Fin k)) (p n : Fin k) : Fin k → ℝ :=
  fun i => if i=p then 1 else if i=n then -1 else if i∈S then 0 else a.w₃ i

def signedNet (a : Network N m k) (S : Finset (Fin k)) (p n : Fin k)
    (L : Fin m → ℝ) (η : ℝ) : Network N m k :=
  {a with
    W₂ := signedChordRows a S p n L
    b₂ := signedChordBiases a S p n η
    w₃ := readout a S p n}

def splitNet (a : Network N m k) (S : Finset (Fin k)) (p n : Fin k)
    (Q R : Fin m → ℝ) (q r : ℝ) : Network N m k :=
  {a with
    W₂ := fun i => if i=p then Q else if i=n then R else if i∈S then 0 else a.W₂ i
    b₂ := fun i => if i=p then q else if i=n then r else if i∈S then 0 else a.b₂ i
    w₃ := readout a S p n}

theorem physical_ext (a b : Network N m k)
    (hA : a.W₁=b.W₁) (hβ : a.b₁=b.b₁) (hC : a.W₂=b.W₂)
    (hδ : a.b₂=b.b₂) (hd : a.w₃=b.w₃) (hθ : a.b₃=b.b₃) : a=b := by
  cases a
  cases b
  congr 1

def AgreeOutside (a b : Network N m k) (S : Finset (Fin k)) : Prop :=
  b.W₁=a.W₁ ∧ b.b₁=a.b₁ ∧ b.b₃=a.b₃ ∧
    ∀ i∉S, b.W₂ i=a.W₂ i ∧ b.b₂ i=a.b₂ i ∧ b.w₃ i=a.w₃ i

theorem signedNet_congr_source (a b : Network N m k) (S : Finset (Fin k))
    (p n : Fin k) (L : Fin m → ℝ) (η : ℝ) (h : AgreeOutside a b S) :
    signedNet b S p n L η=signedNet a S p n L η := by
  apply physical_ext
  · exact h.1
  · exact h.2.1
  · funext i
    by_cases hip : i=p <;> by_cases hin : i=n <;> by_cases hi : i∈S <;>
      simp only [signedNet,signedChordRows,hip,hin,hi,if_true,if_false]
    exact (h.2.2.2 i hi).1
  · funext i
    by_cases hip : i=p <;> by_cases hin : i=n <;> by_cases hi : i∈S <;>
      simp only [signedNet,signedChordBiases,hip,hin,hi,if_true,if_false]
    exact (h.2.2.2 i hi).2.1
  · funext i
    by_cases hip : i=p <;> by_cases hin : i=n <;> by_cases hi : i∈S <;>
      simp only [signedNet,readout,hip,hin,hi,if_true,if_false]
    exact (h.2.2.2 i hi).2.2
  · exact h.2.2.1

theorem splitNet_congr_source (a b : Network N m k) (S : Finset (Fin k))
    (p n : Fin k) (Q R : Fin m → ℝ) (q r : ℝ) (h : AgreeOutside a b S) :
    splitNet b S p n Q R q r=splitNet a S p n Q R q r := by
  apply physical_ext
  · exact h.1
  · exact h.2.1
  · funext i
    by_cases hip : i=p <;> by_cases hin : i=n <;> by_cases hi : i∈S <;>
      simp only [splitNet,hip,hin,hi,if_true,if_false]
    exact (h.2.2.2 i hi).1
  · funext i
    by_cases hip : i=p <;> by_cases hin : i=n <;> by_cases hi : i∈S <;>
      simp only [splitNet,hip,hin,hi,if_true,if_false]
    exact (h.2.2.2 i hi).2.1
  · funext i
    by_cases hip : i=p <;> by_cases hin : i=n <;> by_cases hi : i∈S <;>
      simp only [splitNet,readout,hip,hin,hi,if_true,if_false]
    exact (h.2.2.2 i hi).2.2
  · exact h.2.2.1

variable [NeZero N]

theorem unusedSecond_joinedIn (a : Network N m k) (ha : ∀ x,a.eval x=Maximum N x)
    (i : Fin k) (hi : a.w₃ i=0) (row : Fin m → ℝ) (bias : ℝ) :
    JoinedIn (ExactSet N m k) a (replaceSecond a i row bias) := by
  apply JoinedIn.ofLine (continuous_unusedSecondMove a i row bias).continuousOn
    (unusedSecondMove_zero a i row bias) (unusedSecondMove_one a i row bias)
  rintro _ ⟨t,_ht,rfl⟩ x
  rw [unusedSecondMove_eval a i hi row bias t x]
  exact ha x

theorem dormantOutput_joinedIn (a : Network N m k) (ha : ∀ x,a.eval x=Maximum N x)
    (i : Fin k) (hzero : ∀ x,relu (preact a.W₁ a.b₁ (a.W₂ i) (a.b₂ i) x)=0) (d : ℝ) :
    JoinedIn (ExactSet N m k) a (withOutput a (Function.update a.w₃ i d) a.b₃) := by
  have heval (x : Point N) : (withOutput a (Function.update a.w₃ i d) a.b₃).eval x=a.eval x := by
    change (∑ j, Function.update a.w₃ i d j*relu (preact a.W₁ a.b₁ (a.W₂ j) (a.b₂ j) x))+a.b₃=
      (∑ j,a.w₃ j*relu (preact a.W₁ a.b₁ (a.W₂ j) (a.b₂ j) x))+a.b₃
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hji : j=i
    · subst j
      rw [hzero x]
      simp
    · simp only [Function.update_noteq hji]
  apply JoinedIn.ofLine (continuous_interpolateOutput a (Function.update a.w₃ i d) a.b₃).continuousOn
    (interpolateOutput_zero _ _ _) (interpolateOutput_one _ _ _)
  rintro _ ⟨t,_ht,rfl⟩ x
  rw [interpolateOutput_eval,heval x,ha x]
  ring

theorem clearZeroRows_joinedIn (a : Network N m k) (ha : ∀ x,a.eval x=Maximum N x)
    (D : Finset (Fin k)) (hrow : ∀ i∈D,a.W₂ i=0) (hbias : ∀ i∈D,a.b₂ i=0) :
    JoinedIn (ExactSet N m k) a (withOutput a (eraseClusterOutput a.w₃ D) a.b₃) := by
  apply eraseCancelingCluster_joinedIn_exact ⟨a,ha⟩ D
  intro x
  apply Finset.sum_eq_zero
  intro i hi
  simp [preact,hrow i hi,hbias i hi,relu]

end MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
