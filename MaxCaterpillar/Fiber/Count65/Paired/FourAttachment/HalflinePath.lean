import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.OffsetPath

/-! # Contract a half-line in an actual oriented completion

Natural first-layer preactivations supply the two opposite coordinate halves.
Surjective physical probes turn carrier nonnegativity into the scalar
coefficient constraints; the conclusion is joinedness of actual networks.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption
variable {N m k : ℕ}

noncomputable def halflineOffsets (P Q : Fin m → ℝ) (S T : Finset (Fin k))
    (c e : ℝ) : Fin k → Fin m → ℝ :=
  fun i l => (if i∈S then c else 0)*P l+(if i∈T then e else 0)*Q l

lemma halflineOffsets_preact (A : Fin m → Point N) (β P Q : Fin m → ℝ)
    (S T : Finset (Fin k)) (c e u : ℝ) (x : Point N)
    (hP : preact A β P 0 x=relu u) (hQ : preact A β Q 0 x=relu (-u)) (i : Fin k) :
    preact A β (halflineOffsets P Q S T c e i) 0 x=
      (if i∈S then c*relu u else 0)+(if i∈T then e*relu (-u) else 0) := by
  have he : preact A β (halflineOffsets P Q S T c e i) 0 x=
      (if i∈S then c else 0)*preact A β P 0 x+
        (if i∈T then e else 0)*preact A β Q 0 x := by
    simp only [preact,halflineOffsets,add_mul,Finset.sum_add_distrib,
      mul_assoc,← Finset.mul_sum,add_zero]
  rw [he,hP,hQ]
  by_cases hs : i∈S <;> by_cases ht : i∈T <;> simp [hs,ht]

lemma halflineOffsets_atomBalance (A : Fin m → Point N) (β P Q : Fin m → ℝ)
    (S T : Finset (Fin k)) (c e u : ℝ) (j : Fin k → ℝ)
    (hS : (∑ i in S,j i)=0) (hT : (∑ i in T,j i)=0) (hj : (∑ i,j i)=1)
    (x : Point N) (hP : preact A β P 0 x=relu u) (hQ : preact A β Q 0 x=relu (-u)) :
    Paired65.AtomBalance j (fun i => preact A β (halflineOffsets P Q S T c e i) 0 x) := by
  apply Paired65.atomBalance_of_relu_identity
  intro z
  simp_rw [halflineOffsets_preact A β P Q S T c e u x hP hQ]
  rcases le_total 0 u with hu|hu
  · have hn : relu (-u)=0 := relu_of_nonpos (neg_nonpos.mpr hu)
    simp only [hn,mul_zero,ite_self,add_zero]
    exact canceled_group_relu_identity j S hS hj (c*relu u) z
  · have hp : relu u=0 := relu_of_nonpos hu
    simp only [hp,mul_zero,ite_self,zero_add]
    exact canceled_group_relu_identity j T hT hj (e*relu (-u)) z

lemma sum_indicator_mul (w : Fin k → ℝ) (S : Finset (Fin k)) (z : ℝ) :
    (∑ i,w i*(if i∈S then z else 0))=(∑ i in S,w i)*z := by
  rw [Finset.sum_mul]
  have hfilter : Finset.univ.filter (fun i => i∈S)=S := by ext i; simp
  rw [← hfilter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i∈S <;> simp [hi]

lemma halflineOffsets_carrier (A : Fin m → Point N) (β B D P Q : Fin m → ℝ)
    (S T : Finset (Fin k)) (c e l n u v q r : ℝ)
    (j : Fin k → ℝ) (flip : Fin k → Bool) (x : Point N)
    (hP : preact A β P 0 x=relu u) (hQ : preact A β Q 0 x=relu (-u))
    (hlin : preact A β B 0 x+(∑ i,orientationWeight j flip i)*preact A β D 0 x=
      (∑ i,orientationWeight j flip i)*q+(1-∑ i,orientationWeight j flip i)*r+l*u+n*v) :
    preact A β (carrierRow j flip B D (halflineOffsets P Q S T c e)) 0 x=
      halflineCarrier (∑ i,orientationWeight j flip i) l n
        (c*∑ i in S,orientationWeight j flip i) (e*∑ i in T,orientationWeight j flip i)
        u v q r := by
  rw [preact_carrierRow,hlin]
  simp_rw [halflineOffsets_preact A β P Q S T c e u x hP hQ,mul_add]
  rw [Finset.sum_add_distrib,sum_indicator_mul,sum_indicator_mul]
  unfold halflineCarrier
  ring

theorem continuous_halflineOffsets (P Q : Fin m → ℝ) (S T : Finset (Fin k))
    (c e : ℝ → ℝ) (hc : Continuous c) (he : Continuous e) :
    Continuous (fun t => halflineOffsets P Q S T (c t) (e t)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro l
  change Continuous (fun t => (if i∈S then c t else 0)*P l+(if i∈T then e t else 0)*Q l)
  by_cases hs : i∈S <;> by_cases ht : i∈T <;> simp only [hs,ht,if_true,if_false]
  · exact (hc.mul continuous_const).add (he.mul continuous_const)
  · exact (hc.mul continuous_const).add (continuous_const.mul continuous_const)
  · exact (continuous_const.mul continuous_const).add (he.mul continuous_const)
  · exact (continuous_const.mul continuous_const).add (continuous_const.mul continuous_const)

/-- The only geometrical data are actual coordinate evaluations and actual
inputs realizing every independent anchor/increment probe. -/
theorem halflineCompletion_contract [NeZero N]
    (A : Fin m → Point N) (β B D P Q : Fin m → ℝ)
    (S T : Finset (Fin k)) (c e l n : ℝ) (j : Fin k → ℝ) (flip : Fin k → Bool)
    (hS : (∑ i in S,j i)=0) (hT : (∑ i in T,j i)=0) (hj : (∑ i,j i)=1)
    (u v q r : Point N → ℝ) (hq : ∀ x,0≤q x) (hr : ∀ x,0≤r x)
    (hP : ∀ x,preact A β P 0 x=relu (u x))
    (hQ : ∀ x,preact A β Q 0 x=relu (-u x))
    (hlin : ∀ x,preact A β B 0 x+(∑ i,orientationWeight j flip i)*preact A β D 0 x=
      (∑ i,orientationWeight j flip i)*q x+(1-∑ i,orientationWeight j flip i)*r x+l*u x+n*v x)
    (hprobe : ∀ u₀ v₀ q₀ r₀ : ℝ,0≤q₀ → 0≤r₀ →
      ∃ x,u x=u₀ ∧ v x=v₀ ∧ q x=q₀ ∧ r x=r₀)
    (hg : ∀ x,0≤preact A β (carrierRow j flip B D (halflineOffsets P Q S T c e)) 0 x)
    (hexact : ∀ x,preact A β B 0 x+relu (preact A β D 0 x)=Maximum N x) :
    (0≤l ∧ JoinedIn (ExactSet N m (k+1))
      (orientedCompletionNet A β B D (halflineOffsets P Q S T c e) j flip)
      (orientedCompletionNet A β B D (halflineOffsets P Q S T 0 e) j flip)) ∨
    (l≤0 ∧ JoinedIn (ExactSet N m (k+1))
      (orientedCompletionNet A β B D (halflineOffsets P Q S T c e) j flip)
      (orientedCompletionNet A β B D (halflineOffsets P Q S T c 0) j flip)) := by
  let s := ∑ i,orientationWeight j flip i
  let cp := c*∑ i in S,orientationWeight j flip i
  let cn := e*∑ i in T,orientationWeight j flip i
  have hpos : ∀ u₀ v₀ q₀ r₀ : ℝ,0≤q₀ → 0≤r₀ →
      0≤halflineCarrier s l n cp cn u₀ v₀ q₀ r₀ := by
    intro u₀ v₀ q₀ r₀ hq₀ hr₀
    obtain ⟨x,hux,hvx,hqx,hrx⟩ := hprobe u₀ v₀ q₀ r₀ hq₀ hr₀
    have h := hg x
    rw [halflineOffsets_carrier A β B D P Q S T c e l n (u x) (v x) (q x) (r x)
      j flip x (hP x) (hQ x) (hlin x),hux,hvx,hqx,hrx] at h
    exact h
  rcases le_total 0 l with hl|hl
  · left
    refine ⟨hl,?_⟩
    let F := fun t : ℝ => halflineOffsets P Q S T ((1-t)*c) e
    have hpath : JoinedIn (ExactSet N m (k+1))
        (orientedCompletionNet A β B D (F 0) j flip)
        (orientedCompletionNet A β B D (F 1) j flip) := by
      apply orientedCompletionNet_joinedIn_exact A β B D F
        (continuous_halflineOffsets P Q S T _ _ (by continuity) continuous_const) j flip
      · intro t _ x
        exact halflineOffsets_atomBalance A β P Q S T ((1-t)*c) e (u x) j hS hT hj x (hP x) (hQ x)
      · intro t ht x
        rw [halflineOffsets_carrier A β B D P Q S T ((1-t)*c) e l n (u x) (v x) (q x) (r x)
          j flip x (hP x) (hQ x) (hlin x)]
        have hp := contract_positive_halfline s l n cp cn hpos hl ht.1 ht.2
          (u x) (v x) (q x) (r x) (hq x) (hr x)
        dsimp only [s,cp,cn] at hp
        convert hp using 1 <;> ring
      · exact hexact
    simpa only [F,sub_zero,one_mul,sub_self,zero_mul] using hpath
  · right
    refine ⟨hl,?_⟩
    let F := fun t : ℝ => halflineOffsets P Q S T c ((1-t)*e)
    have hpath : JoinedIn (ExactSet N m (k+1))
        (orientedCompletionNet A β B D (F 0) j flip)
        (orientedCompletionNet A β B D (F 1) j flip) := by
      apply orientedCompletionNet_joinedIn_exact A β B D F
        (continuous_halflineOffsets P Q S T _ _ continuous_const (by continuity)) j flip
      · intro t _ x
        exact halflineOffsets_atomBalance A β P Q S T c ((1-t)*e) (u x) j hS hT hj x (hP x) (hQ x)
      · intro t ht x
        rw [halflineOffsets_carrier A β B D P Q S T c ((1-t)*e) l n (u x) (v x) (q x) (r x)
          j flip x (hP x) (hQ x) (hlin x)]
        have hp := contract_negative_halfline s l n cp cn hpos hl ht.1 ht.2
          (u x) (v x) (q x) (r x) (hq x) (hr x)
        dsimp only [s,cp,cn] at hp
        convert hp using 1 <;> ring
      · exact hexact
    simpa only [F,sub_zero,one_mul,sub_self,zero_mul] using hpath

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
