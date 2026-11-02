import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.SupportCases
import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.Compression
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointScaledBridge

/-! # Attachment of the exhaustive extracted four-atom offset families -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption
variable {N m k : ℕ}

lemma orientedRow_preact (A : Fin m → Point N) (β D F : Fin m → ℝ)
    (flip : Bool) (x : Point N) :
    preact A β (if flip then -(D-F) else D-F) 0 x=
      if flip then -(preact A β D 0 x-preact A β F 0 x)
      else preact A β D 0 x-preact A β F 0 x := by
  cases flip
  · exact preact_sub_zero A β D F x
  · have hn : preact A β (-(D-F)) 0 x= -preact A β (D-F) 0 x := by
      simpa only [neg_zero] using preact_neg A β (D-F) 0 x
    simpa only [if_true,preact_sub_zero] using hn

lemma orientedCompletionNet_eval_difference (A : Fin m → Point N) (β B D : Fin m → ℝ)
    (F : Fin k → Fin m → ℝ) (j : Fin k → ℝ) (flip : Fin k → Bool) (x : Point N)
    (hbal : Paired65.AtomBalance j (fun i => preact A β (F i) 0 x)) :
    (orientedCompletionNet A β B D F j flip).eval x=
      relu (preact A β (carrierRow j flip B D F) 0 x)-
        preact A β (carrierRow j flip B D F) 0 x+
          (preact A β B 0 x+relu (preact A β D 0 x)) := by
  have he := oriented_comparisons_sum A β B D F j flip x hbal
  simp_rw [← orientedRow_preact] at he
  have hs : (orientedCompletionNet A β B D F j flip).eval x=
      relu (preact A β (carrierRow j flip B D F) 0 x)+
        (preact A β B 0 x+relu (preact A β D 0 x)-
          preact A β (carrierRow j flip B D F) 0 x) := by
    rw [Network.eval,Fin.sum_univ_succ]
    simp only [orientedCompletionNet,Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,one_mul,add_zero]
    simpa only [preact,add_zero] using congrArg
      (fun z => relu (preact A β (carrierRow j flip B D F) 0 x)+z) he
  rw [hs]
  ring

/-- For the forced-row representative, physical carrier positivity follows
from exactness, rather than being a new hypothesis on a deformation endpoint. -/
theorem orientedCompletion_carrier_nonneg_of_exact [NeZero N]
    (A : Fin m → Point N) (β B D : Fin m → ℝ)
    (F : Fin k → Fin m → ℝ) (j : Fin k → ℝ) (flip : Fin k → Bool)
    (hbal : ∀ x,Paired65.AtomBalance j (fun i => preact A β (F i) 0 x))
    (hexact : ∀ x,(orientedCompletionNet A β B D F j flip).eval x=Maximum N x)
    (hmax : ∀ x,preact A β B 0 x+relu (preact A β D 0 x)=Maximum N x) :
    ∀ x,0≤preact A β (carrierRow j flip B D F) 0 x := by
  intro x
  have he := orientedCompletionNet_eval_difference A β B D F j flip x (hbal x)
  rw [hexact x,hmax x] at he
  have hp := relu_nonneg (preact A β (carrierRow j flip B D F) 0 x)
  linarith only [he,hp]

lemma commonSupport_atomBalance (A : Fin m → Point N) (β H : Fin m → ℝ)
    (j : Fin k → ℝ) (S : Finset (Fin k))
    (hS : (∑ i in S,j i)=0) (hj : (∑ i,j i)=1) (x : Point N) :
    Paired65.AtomBalance j (fun i => preact A β (if i∈S then H else 0) 0 x) := by
  apply Paired65.atomBalance_of_relu_identity
  intro z
  have hoff (i : Fin k) : preact A β (if i∈S then H else 0) 0 x=
      if i∈S then preact A β H 0 x else 0 := by
    by_cases hi : i∈S <;> simp [hi,preact]
  simp_rw [hoff]
  exact canceled_group_relu_identity j S hS hj _ z

lemma halflineOffsets_left_zero (P Q : Fin m → ℝ) (S T : Finset (Fin k)) (e : ℝ) :
    halflineOffsets P Q S T 0 e=(fun i => if i∈T then e • Q else 0) := by
  funext i l
  by_cases hi : i∈T <;> by_cases hs : i∈S <;> simp [halflineOffsets,hi,hs]

lemma halflineOffsets_right_zero (P Q : Fin m → ℝ) (S T : Finset (Fin k)) (c : ℝ) :
    halflineOffsets P Q S T c 0=(fun i => if i∈S then c • P else 0) := by
  funext i l
  by_cases hi : i∈S <;> by_cases ht : i∈T <;> simp [halflineOffsets,hi,ht]

lemma paired_negative_diagonal (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) :
    preact (pairedRows U) 0 (comparisonRow U) 0 (fun _ => -1)=0 ∧
    preact (pairedRows U) 0 (baselineRow U) 0 (fun _ => -1)<0 := by
  rw [paired_preact_eq_endpointForm,paired_preact_eq_endpointForm,
    comparisonRow_form U hU,baselineRow_form U hU]
  norm_num

/-- Every actual exact-parameter path descends to the genuine symmetry
quotient. Endpoint proofs are irrelevant; no extra identification is used. -/
theorem quotient_joined_of_joinedIn {N m r : ℕ} [NeZero N]
    {a b : Network N m r} (ha : ∀ x,a.eval x=Maximum N x)
    (hb : ∀ x,b.eval x=Maximum N x) (h : JoinedIn (ExactSet N m r) a b) :
    Joined (quotientMk (⟨a,ha⟩ : ExactFiber N m r)) (quotientMk (⟨b,hb⟩ : ExactFiber N m r)) := by
  exact ⟨h.joined_subtype.somePath.map quotientMk_continuous⟩

noncomputable def extractedFourFamily (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 4 ≃ NetworkAtoms net) : Network 4 6 5 :=
  orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
    (fun i => codeOffsetRow net U (e i)) (fun i => networkAtomJump net (e i)) (fourAtomFlip net e)

lemma extractedFourFamily_exact (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hcode : codeDet U≠0)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (e : Fin 4 ≃ NetworkAtoms net)
    (hg : ∀ x,0≤preact (pairedRows U) 0
      (carrierRow (fun i => networkAtomJump net (e i)) (fourAtomFlip net e)
        (baselineRow U) (comparisonRow U) (fun i => codeOffsetRow net U (e i))) 0 x) :
    ∀ x,(extractedFourFamily net U e).eval x=Maximum 4 x := by
  intro x
  rw [extractedFourFamily,orientedCompletionNet_eval _ _ _ _ _ _ _ x
    (codeOffsetRow_balance net U hU hcode hb hnet e x) (hg x)]
  exact paired_max_decomposition U hcode x

noncomputable def extractedFourFamilyPoint (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hcode : codeDet U≠0)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (e : Fin 4 ≃ NetworkAtoms net)
    (hg : ∀ x,0≤preact (pairedRows U) 0
      (carrierRow (fun i => networkAtomJump net (e i)) (fourAtomFlip net e)
        (baselineRow U) (comparisonRow U) (fun i => codeOffsetRow net U (e i))) 0 x) :
    ExactFiber 4 6 5 :=
  ⟨extractedFourFamily net U e,extractedFourFamily_exact net U hU hcode hb hnet e hg⟩

lemma network_atom_jumps_sum (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (e : Fin 4 ≃ NetworkAtoms net) : (∑ i,networkAtomJump net (e i))=1 := by
  have he := Fintype.sum_equiv e (fun i : Fin 4 => networkAtomJump net (e i))
    (networkAtomJump net) (fun _ => rfl)
  rw [he]
  exact atomBalance_sum_weights _ _ (network_effective_atomBalance net U hU hb hnet 0 0)

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
