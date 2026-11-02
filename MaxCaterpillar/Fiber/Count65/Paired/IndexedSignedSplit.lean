import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Basic

/-! An actual indexed split readout becomes a signed pair using a spare slot.
All first parameters, the output bias, and every spectator remain fixed. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Absorption QuadrantGroups BaselineAttachment Frontier
variable {N m k : ℕ}

private theorem sum_three (p z n : Fin k) (hpz : p ≠ z) (hpn : p ≠ n)
    (hzn : z ≠ n) (f : Fin k → ℝ) :
    (∑ i, f i) = f p+f z+f n+
      ∑ i in (((Finset.univ : Finset (Fin k)).erase p).erase z).erase n, f i := by
  have hz : z ∈ (Finset.univ : Finset (Fin k)).erase p := by simp [Ne.symm hpz]
  have hn : n ∈ ((Finset.univ : Finset (Fin k)).erase p).erase z := by
    simp [Ne.symm hpn,Ne.symm hzn]
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ p),
    ← Finset.add_sum_erase _ f hz,← Finset.add_sum_erase _ f hn]
  ring

/-- The reverse split homotopy. At parameter one the spare is inactive;
at zero it carries the negative of the literal signed preactivation. -/
def indexedSignedSplitPhase (a : Network N m k) (S : Finset (Fin k))
    (p n z : Fin k) (Q R : Fin m → ℝ) (q r t : ℝ) : Network N m k :=
  {a with
    W₂ := fun i => if i=p then (fun j => Q j+(t-1)*R j)
      else if i=z then (fun j => -(Q j+(t-1)*R j))
      else if i=n then R else if i∈S then 0 else a.W₂ i
    b₂ := fun i => if i=p then q+(t-1)*r else if i=z then -(q+(t-1)*r)
      else if i=n then r else if i∈S then 0 else a.b₂ i
    w₃ := fun i => if i=p then 1 else if i=z then -1 else if i=n then -t
      else if i∈S then 0 else a.w₃ i}

private theorem continuous_phase (a : Network N m k) (S : Finset (Fin k))
    (p n z : Fin k) (Q R : Fin m → ℝ) (q r : ℝ) :
    Continuous (indexedSignedSplitPhase a S p n z Q R q r) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,?_,continuous_const⟩
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hip : i=p <;> by_cases hiz : i=z <;> by_cases hin : i=n <;>
      by_cases hi : i∈S <;> simp [indexedSignedSplitPhase,hip,hiz,hin,hi] <;> continuity
  · apply continuous_pi
    intro i
    by_cases hip : i=p <;> by_cases hiz : i=z <;> by_cases hin : i=n <;>
      by_cases hi : i∈S <;> simp [indexedSignedSplitPhase,hip,hiz,hin,hi] <;> continuity
  · apply continuous_pi
    intro i
    by_cases hip : i=p <;> by_cases hiz : i=z <;> by_cases hin : i=n <;>
      by_cases hi : i∈S <;> simp [indexedSignedSplitPhase,hip,hiz,hin,hi] <;> continuity

private theorem phase_eval (a : Network N m k) (S : Finset (Fin k))
    (p n z : Fin k) (hpn : p≠n) (hpz : p≠z) (hnz : n≠z)
    (Q R : Fin m → ℝ) (q r t : ℝ)
    (hR : ∀ x,0≤preact a.W₁ a.b₁ R r x) (x : Point N) :
    (indexedSignedSplitPhase a S p n z Q R q r t).eval x =
      (indexedSignedSplitPhase a S p n z Q R q r 1).eval x := by
  let rest := (((Finset.univ : Finset (Fin k)).erase p).erase z).erase n
  let f := fun t i => (indexedSignedSplitPhase a S p n z Q R q r t).w₃ i *
    relu (preact a.W₁ a.b₁
      ((indexedSignedSplitPhase a S p n z Q R q r t).W₂ i)
      ((indexedSignedSplitPhase a S p n z Q R q r t).b₂ i) x)
  have hrest : (∑ i in rest,f t i) = ∑ i in rest,f 1 i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i≠n := (Finset.mem_erase.mp hi).1
    have hiz : i≠z := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hip : i≠p := (Finset.mem_erase.mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2).1
    simp [f,indexedSignedSplitPhase,hip,hiz,hin]
  have hthree (u : ℝ) : f u p+f u z+f u n =
      preact a.W₁ a.b₁ Q q x-preact a.W₁ a.b₁ R r x := by
    simp only [f,indexedSignedSplitPhase,if_pos rfl,if_neg (Ne.symm hpz),
      if_neg (Ne.symm hpn),if_neg hnz,if_true,one_mul,neg_one_mul]
    rw [preact_neg,preact_addmul,relu_of_nonneg (hR x)]
    have hh := relu_sub_relu_neg
      (preact a.W₁ a.b₁ Q q x+(u-1)*preact a.W₁ a.b₁ R r x)
    linarith only [hh]
  change (∑ i,f t i)+a.b₃ = (∑ i,f 1 i)+a.b₃
  rw [sum_three p z n hpz hpn (Ne.symm hnz) (f t),
    sum_three p z n hpz hpn (Ne.symm hnz) (f 1),hthree,hthree,hrest]

variable [NeZero N]

/-- A positive-minus-positive physical encoding can be attached to the
literal signed encoding, using any third selected spare slot. -/
theorem splitNet_joinedIn_signedNet (a : Network N m k) (S : Finset (Fin k))
    (p n z : Fin k) (hp : p∈S) (hn : n∈S) (hz : z∈S)
    (hpn : p≠n) (hpz : p≠z) (hnz : n≠z)
    (Q R : Fin m → ℝ) (q r : ℝ)
    (hQ : ∀ x,0≤preact a.W₁ a.b₁ Q q x)
    (hR : ∀ x,0≤preact a.W₁ a.b₁ R r x)
    (ha : ∀ x,(splitNet a S p n Q R q r).eval x=Maximum N x) :
    JoinedIn (ExactSet N m k) (splitNet a S p n Q R q r)
      (signedNet a S p z (fun j => Q j-R j) (q-r)) := by
  let src := splitNet a S p n Q R q r
  let prep := replaceSecond src z (-Q) (-q)
  have hzout : src.w₃ z=0 := by simp [src,splitNet,readout,Ne.symm hpz,Ne.symm hnz,hz]
  have hprep := unusedSecond_joinedIn src ha z hzout (-Q) (-q)
  have hprepex : ∀ x,prep.eval x=Maximum N x := hprep.target_mem
  have hdorm : ∀ x,relu (preact prep.W₁ prep.b₁ (prep.W₂ z) (prep.b₂ z) x)=0 := by
    intro x
    simp only [prep,src,replaceSecond,splitNet,Function.update_same]
    change relu (preact a.W₁ a.b₁ (fun j => -Q j) (-q) x)=0
    rw [preact_neg,relu_of_nonpos (neg_nonpos.mpr (hQ x))]
  have hout := dormantOutput_joinedIn prep hprepex z hdorm (-1)
  have hprepared : withOutput prep (Function.update prep.w₃ z (-1)) prep.b₃ =
      indexedSignedSplitPhase a S p n z Q R q r 1 := by
    apply physical_ext <;> try rfl
    · funext i j
      by_cases hip : i=p
      · subst i
        simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
      · by_cases hin : i=n
        · subst i
          simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
        · by_cases hiz : i=z
          · subst i
            simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
          · simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,hip,hin,hiz]
    · funext i
      by_cases hip : i=p
      · subst i
        simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
      · by_cases hin : i=n
        · subst i
          simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
        · by_cases hiz : i=z
          · subst i
            simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
          · simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,hip,hin,hiz]
    · funext i
      by_cases hip : i=p
      · subst i
        simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,readout,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
      · by_cases hin : i=n
        · subst i
          simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,readout,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
        · by_cases hiz : i=z
          · subst i
            simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,readout,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
          · simp [prep,src,replaceSecond,splitNet,indexedSignedSplitPhase,withOutput,readout,hip,hin,hiz]
  rw [hprepared] at hout
  have hone : ∀ x,(indexedSignedSplitPhase a S p n z Q R q r 1).eval x=Maximum N x :=
    hout.target_mem
  have hphase : JoinedIn (ExactSet N m k)
      (indexedSignedSplitPhase a S p n z Q R q r 0)
      (indexedSignedSplitPhase a S p n z Q R q r 1) := by
    apply JoinedIn.ofLine (continuous_phase a S p n z Q R q r).continuousOn rfl rfl
    rintro _ ⟨t,_ht,rfl⟩ x
    exact (phase_eval a S p n z hpn hpz hnz Q R q r t hR x).trans (hone x)
  have hzero : (indexedSignedSplitPhase a S p n z Q R q r 0).w₃ n=0 := by
    simp [indexedSignedSplitPhase,Ne.symm hpn,hnz]
  have hclean := unusedSecond_joinedIn
    (indexedSignedSplitPhase a S p n z Q R q r 0) hphase.source_mem n hzero 0 0
  have hcleaned : replaceSecond (indexedSignedSplitPhase a S p n z Q R q r 0) n 0 0 =
      signedNet a S p z (fun j => Q j-R j) (q-r) := by
    apply physical_ext <;> try rfl
    · funext i j
      by_cases hip : i=p
      · subst i
        simp [replaceSecond,indexedSignedSplitPhase,signedNet,signedChordRows,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]; ring
      · by_cases hin : i=n
        · subst i
          simp [replaceSecond,indexedSignedSplitPhase,signedNet,signedChordRows,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
        · by_cases hiz : i=z
          · subst i
            simp [replaceSecond,indexedSignedSplitPhase,signedNet,signedChordRows,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]; ring
          · simp [replaceSecond,indexedSignedSplitPhase,signedNet,signedChordRows,hip,hin,hiz]
    · funext i
      by_cases hip : i=p
      · subst i
        simp [replaceSecond,indexedSignedSplitPhase,signedNet,signedChordBiases,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]; ring
      · by_cases hin : i=n
        · subst i
          simp [replaceSecond,indexedSignedSplitPhase,signedNet,signedChordBiases,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
        · by_cases hiz : i=z
          · subst i
            simp [replaceSecond,indexedSignedSplitPhase,signedNet,signedChordBiases,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]; ring
          · simp [replaceSecond,indexedSignedSplitPhase,signedNet,signedChordBiases,hip,hin,hiz]
    · funext i
      by_cases hip : i=p
      · subst i
        simp [replaceSecond,indexedSignedSplitPhase,signedNet,readout,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
      · by_cases hin : i=n
        · subst i
          simp [replaceSecond,indexedSignedSplitPhase,signedNet,readout,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
        · by_cases hiz : i=z
          · subst i
            simp [replaceSecond,indexedSignedSplitPhase,signedNet,readout,hpn,hpz,hnz,Ne.symm hpn,Ne.symm hpz,Ne.symm hnz,hp,hn,hz]
          · simp [replaceSecond,indexedSignedSplitPhase,signedNet,readout,hip,hin,hiz]
  rw [hcleaned] at hclean
  exact hprep.trans (hout.trans (hphase.symm.trans hclean))

/-- The same bridge for a raw actual network: the three slots may be any
physical indices, and the zero-output spare has arbitrary incoming parameters.
Every other physical neuron remains literally unchanged at the endpoint. -/
theorem indexed_split_joinedIn_signed (a : Network N m k) (p n z : Fin k)
    (hpn : p≠n) (hpz : p≠z) (hnz : n≠z)
    (hpout : a.w₃ p=1) (hnout : a.w₃ n= -1) (hzout : a.w₃ z=0)
    (hQ : ∀ x,0≤preact a.W₁ a.b₁ (a.W₂ p) (a.b₂ p) x)
    (hR : ∀ x,0≤preact a.W₁ a.b₁ (a.W₂ n) (a.b₂ n) x)
    (ha : ∀ x,a.eval x=Maximum N x) :
    JoinedIn (ExactSet N m k) a
      (signedNet a {p,n,z} p z (fun j => a.W₂ p j-a.W₂ n j) (a.b₂ p-a.b₂ n)) := by
  have hclear := unusedSecond_joinedIn a ha z hzout 0 0
  have heq : replaceSecond a z 0 0 =
      splitNet a {p,n,z} p n (a.W₂ p) (a.W₂ n) (a.b₂ p) (a.b₂ n) := by
    apply physical_ext <;> try rfl
    · funext i j
      by_cases hip : i=p
      · subst i
        simp [replaceSecond,splitNet,hpz]
      · by_cases hin : i=n
        · subst i
          simp [replaceSecond,splitNet,hpn,hnz,Ne.symm hpn]
        · by_cases hiz : i=z
          · subst i
            simp [replaceSecond,splitNet,Ne.symm hpz,Ne.symm hnz]
          · simp [replaceSecond,splitNet,hip,hin,hiz]
    · funext i
      by_cases hip : i=p
      · subst i
        simp [replaceSecond,splitNet,hpz]
      · by_cases hin : i=n
        · subst i
          simp [replaceSecond,splitNet,hpn,hnz,Ne.symm hpn]
        · by_cases hiz : i=z
          · subst i
            simp [replaceSecond,splitNet,Ne.symm hpz,Ne.symm hnz]
          · simp [replaceSecond,splitNet,hip,hin,hiz]
    · funext i
      by_cases hip : i=p
      · subst i
        simp [replaceSecond,splitNet,readout,hpout]
      · by_cases hin : i=n
        · subst i
          simp [replaceSecond,splitNet,readout,Ne.symm hpn,hnout]
        · by_cases hiz : i=z
          · subst i
            simp [replaceSecond,splitNet,readout,Ne.symm hpz,Ne.symm hnz,hzout]
          · simp [replaceSecond,splitNet,readout,hip,hin,hiz]
  rw [heq] at hclear
  exact hclear.trans (splitNet_joinedIn_signedNet a {p,n,z} p n z
    (by simp) (by simp) (by simp) hpn hpz hnz (a.W₂ p) (a.W₂ n)
    (a.b₂ p) (a.b₂ n) hQ hR hclear.target_mem)

end MaxCaterpillar.Fiber.Count65.Paired
