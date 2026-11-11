import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound

/-! Explicit simulation of the fully affine skip model by an ordinary network.
All arrays below are primitive unrestricted real parameters. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
open BigOperators
variable {N h₁ h₂ : ℕ}

structure AffineSkipNetwork (N h₁ h₂ : ℕ) where
  A : Fin h₁ → Point N
  b : Fin h₁ → ℝ
  W : Fin h₂ → Fin h₁ → ℝ
  U : Fin h₂ → Point N
  θ : Fin h₂ → ℝ
  d : Fin h₂ → ℝ
  B : Fin h₁ → ℝ
  L : Point N
  β : ℝ

noncomputable def first (net : AffineSkipNetwork N h₁ h₂) (j : Fin h₁) (x : Point N) : ℝ :=
  relu ((∑ i,net.A j i*x i)+net.b j)
noncomputable def inner (net : AffineSkipNetwork N h₁ h₂) (k : Fin h₂) (x : Point N) : ℝ :=
  (∑ j,net.W k j*first net j x)+(∑ i,net.U k i*x i)+net.θ k
noncomputable def outputSkip (net : AffineSkipNetwork N h₁ h₂) (x : Point N) : ℝ :=
  (∑ j,net.B j*first net j x)+(∑ i,net.L i*x i)+net.β
noncomputable def eval (net : AffineSkipNetwork N h₁ h₂) (x : Point N) : ℝ :=
  (∑ k,net.d k*relu (inner net k x))+outputSkip net x

def ofOrdinary (net : Network N h₁ h₂) : AffineSkipNetwork N h₁ h₂ where
  A := net.W₁
  b := net.b₁
  W := net.W₂
  U := 0
  θ := net.b₂
  d := net.w₃
  B := 0
  L := 0
  β := net.b₃

theorem eval_ofOrdinary (net : Network N h₁ h₂) (x : Point N) :
    eval (ofOrdinary net) x=net.eval x := by
  simp only [eval,inner,outputSkip,first,ofOrdinary,Pi.zero_apply,zero_mul,
    Finset.sum_const_zero,add_zero,zero_add,Network.eval]

abbrev FirstIndex (N h₁ : ℕ) := (Fin h₁ ⊕ Fin N) ⊕ Fin N
abbrev OuterIndex (h₂ : ℕ) := Fin h₂ ⊕ Fin 2

def firstIndexEquiv (N h₁ : ℕ) : FirstIndex N h₁ ≃ Fin (h₁+N+N) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin N))).trans finSumFinEquiv
def outerIndexEquiv (h₂ : ℕ) : OuterIndex h₂ ≃ Fin (h₂+2) := finSumFinEquiv

noncomputable def expandedFirst (net : AffineSkipNetwork N h₁ h₂) : FirstIndex N h₁ → Point N :=
  Sum.elim (Sum.elim net.A (fun a i => if i=a then 1 else 0))
    (fun a i => if i=a then -1 else 0)
noncomputable def expandedBias (net : AffineSkipNetwork N h₁ h₂) : FirstIndex N h₁ → ℝ :=
  Sum.elim (Sum.elim net.b (fun _ => 0)) (fun _ => 0)
noncomputable def augmentedRow (C : Fin h₁ → ℝ) (u : Point N) : FirstIndex N h₁ → ℝ :=
  Sum.elim (Sum.elim C u) (fun i => -u i)

noncomputable def expandedOuterRow (net : AffineSkipNetwork N h₁ h₂) :
    OuterIndex h₂ → FirstIndex N h₁ → ℝ :=
  Sum.elim (fun k => augmentedRow (net.W k) (net.U k))
    (fun t => if t=0 then augmentedRow net.B net.L else fun j => -augmentedRow net.B net.L j)
noncomputable def expandedOuterBias (net : AffineSkipNetwork N h₁ h₂) : OuterIndex h₂ → ℝ :=
  Sum.elim net.θ (fun t => if t=0 then net.β else -net.β)
noncomputable def expandedOutputWeight (net : AffineSkipNetwork N h₁ h₂) : OuterIndex h₂ → ℝ :=
  Sum.elim net.d (fun t => if t=0 then 1 else -1)

noncomputable def encode (net : AffineSkipNetwork N h₁ h₂) : Network N (h₁+N+N) (h₂+2) where
  W₁ j := expandedFirst net ((firstIndexEquiv N h₁).symm j)
  b₁ j := expandedBias net ((firstIndexEquiv N h₁).symm j)
  W₂ k j := expandedOuterRow net ((outerIndexEquiv h₂).symm k) ((firstIndexEquiv N h₁).symm j)
  b₂ k := expandedOuterBias net ((outerIndexEquiv h₂).symm k)
  w₃ k := expandedOutputWeight net ((outerIndexEquiv h₂).symm k)
  b₃ := 0

lemma expandedFirst_relu (net : AffineSkipNetwork N h₁ h₂) (x : Point N) :
    ∀ j : FirstIndex N h₁,
      relu ((∑ i,expandedFirst net j i*x i)+expandedBias net j)=
        Sum.elim (Sum.elim (fun j => first net j x) (fun i => relu (x i)))
          (fun i => relu (-x i)) j := by
  classical
  intro j
  rcases j with (j|a)|a
  · rfl
  · simp [expandedFirst,expandedBias]
  · simp [expandedFirst,expandedBias]

lemma augmentedRow_sum (net : AffineSkipNetwork N h₁ h₂) (C : Fin h₁ → ℝ)
    (u : Point N) (x : Point N) :
    (∑ j : FirstIndex N h₁,augmentedRow C u j*
      relu ((∑ i,expandedFirst net j i*x i)+expandedBias net j))=
        (∑ j,C j*first net j x)+(∑ i,u i*x i) := by
  simp only [expandedFirst_relu,Fintype.sum_sum_type,augmentedRow,
    Sum.elim_inl,Sum.elim_inr]
  rw [add_assoc,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  calc
    u i*relu (x i)+ -u i*relu (-x i)=u i*(relu (x i)-relu (-x i)) := by ring
    _ = u i*x i := congrArg (fun z => u i*z) (relu_sub_relu_neg (x i))

lemma encode_inner (net : AffineSkipNetwork N h₁ h₂) (x : Point N)
    (s : OuterIndex h₂) :
    (∑ j,(encode net).W₂ (outerIndexEquiv h₂ s) j*
      relu ((∑ i,(encode net).W₁ j i*x i)+(encode net).b₁ j))+
      (encode net).b₂ (outerIndexEquiv h₂ s)=
      Sum.elim (fun k => inner net k x)
        (fun t => if t=0 then outputSkip net x else -outputSkip net x) s := by
  have he : (∑ j,(encode net).W₂ (outerIndexEquiv h₂ s) j*
      relu ((∑ i,(encode net).W₁ j i*x i)+(encode net).b₁ j))=
      ∑ j : FirstIndex N h₁,expandedOuterRow net s j*
        relu ((∑ i,expandedFirst net j i*x i)+expandedBias net j) := by
    apply Fintype.sum_equiv (firstIndexEquiv N h₁).symm
    intro j
    simp only [encode,Equiv.symm_apply_apply]
  rw [he]
  simp only [encode,Equiv.symm_apply_apply]
  rcases s with k|t
  · exact congrArg (fun z => z+net.θ k) (augmentedRow_sum net (net.W k) (net.U k) x)
  · by_cases ht : t=0
    · simpa only [expandedOuterRow,expandedOuterBias,Sum.elim_inr,if_pos ht,outputSkip] using
        congrArg (fun z => z+net.β) (augmentedRow_sum net net.B net.L x)
    · simp only [expandedOuterRow,expandedOuterBias,Sum.elim_inr,if_neg ht,neg_mul,
        Finset.sum_neg_distrib,augmentedRow_sum,outputSkip]
      ring

/-- Exact simulation with 2N extra first neurons and two extra second neurons. -/
theorem encode_eval (net : AffineSkipNetwork N h₁ h₂) (x : Point N) :
    (encode net).eval x=eval net x := by
  have he : (∑ k,(encode net).w₃ k*relu
      ((∑ j,(encode net).W₂ k j*relu ((∑ i,(encode net).W₁ j i*x i)+(encode net).b₁ j))+
        (encode net).b₂ k))=
      ∑ s : OuterIndex h₂,expandedOutputWeight net s*relu
        (Sum.elim (fun k => inner net k x)
          (fun t => if t=0 then outputSkip net x else -outputSkip net x) s) := by
    apply Fintype.sum_equiv (outerIndexEquiv h₂).symm
    intro k
    have hh := encode_inner net x ((outerIndexEquiv h₂).symm k)
    rw [Equiv.apply_symm_apply] at hh
    rw [hh]
    rfl
  rw [Network.eval,he]
  simp only [encode,add_zero,Fintype.sum_sum_type,expandedOutputWeight,Sum.elim_inl,Sum.elim_inr]
  rw [Fin.sum_univ_two]
  simp only [if_pos rfl,show (1 : Fin 2)≠0 from by decide,if_false,ite_true,one_mul,neg_one_mul]
  have hh := relu_sub_relu_neg (outputSkip net x)
  unfold eval
  linarith only [hh]

theorem second_width_tradeoff_affine_skips (hN : 1040≤N)
    (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,eval net x=Maximum N x) →
      (1/400000000 : ℝ)*min ((N : ℝ)^2)
        ((N : ℝ)^4/((h₁ : ℝ)+2*(N : ℝ)))≤(h₂ : ℝ)+2 := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet
  have hh := NetworkLowerBound.second_width_tradeoff hN (encode net)
    (fun x => (encode_eval net x).trans (hnet x))
  push_cast at hh
  convert hh using 1 <;> ring

theorem encoded_width_slack [NeZero N] (hN : 1040≤N)
    (net : AffineSkipNetwork N h₁ h₂) (hnet : ∀ x,eval net x=Maximum N x) :
    2*(N : ℝ)≤(h₁ : ℝ) ∧ (2 : ℝ)≤(h₂ : ℝ) := by
  have he : ∀ x,(encode net).eval x=Maximum N x :=
    fun x => (encode_eval net x).trans (hnet x)
  have hfirst := first_width_quadratic (encode net) he
  have hsecond := second_width_half (encode net) he
  have hf : 3*(N : ℝ)*(N : ℝ)+12≤6*((h₁ : ℝ)+(N : ℝ)+(N : ℝ))+11*(N : ℝ) := by
    exact_mod_cast hfirst
  have hs : (N : ℝ)≤2*((h₂ : ℝ)+2) := by exact_mod_cast hsecond
  have hn : (1040 : ℝ)≤(N : ℝ) := by exact_mod_cast hN
  constructor
  · nlinarith only [hf,hn]
  · linarith only [hs,hn]

/-- A shift-free tradeoff for arbitrary affine skips, with a factor-four
constant loss relative to the ordinary-network theorem. -/
theorem second_width_tradeoff_affine_skips_unshifted (hN : 1040≤N)
    (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,eval net x=Maximum N x) →
      (1/1600000000 : ℝ)*min ((N : ℝ)^2)
        ((N : ℝ)^4/(h₁ : ℝ))≤(h₂ : ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet
  obtain ⟨hfirst,hsecond⟩ := encoded_width_slack hN net hnet
  have hn : (1040 : ℝ)≤(N : ℝ) := by exact_mod_cast hN
  have hp : (0 : ℝ)<(h₁ : ℝ) := by linarith only [hfirst,hn]
  have hd : (0 : ℝ)<(h₁ : ℝ)+2*(N : ℝ) := by linarith only [hp,hn]
  have hratio : (N : ℝ)^4/(h₁ : ℝ)≤2*((N : ℝ)^4/((h₁ : ℝ)+2*(N : ℝ))) := by
    calc
      _ ≤ (2*(N : ℝ)^4)/((h₁ : ℝ)+2*(N : ℝ)) := by
        apply (div_le_div_iff hp hd).mpr
        have hh := mul_le_mul_of_nonneg_left hfirst (pow_nonneg (by linarith only [hn] : (0 : ℝ)≤N) 4)
        nlinarith only [hh]
      _ = _ := by ring
  have hm : min ((N : ℝ)^2) ((N : ℝ)^4/(h₁ : ℝ))≤
      2*min ((N : ℝ)^2) ((N : ℝ)^4/((h₁ : ℝ)+2*(N : ℝ))) := by
    by_cases hs : (N : ℝ)^2≤(N : ℝ)^4/((h₁ : ℝ)+2*(N : ℝ))
    · rw [min_eq_left hs]
      exact (min_le_left _ _).trans (by nlinarith only [sq_nonneg (N : ℝ)])
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hs))]
      exact (min_le_right _ _).trans hratio
  have hh := second_width_tradeoff_affine_skips hN net hnet
  linarith only [hh,hm,hsecond]

#print axioms encode_eval
#print axioms second_width_tradeoff_affine_skips
#print axioms second_width_tradeoff_affine_skips_unshifted
end MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
