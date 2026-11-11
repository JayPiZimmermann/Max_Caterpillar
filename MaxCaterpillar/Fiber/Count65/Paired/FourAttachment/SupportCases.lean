import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.ActualRepresentation

/-! # Explicit physical row alternatives for all actual four-atom offsets -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption

lemma reindex_filtered_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin 4 ≃ ι) (S : Finset ι) (j : ι → ℝ) :
    (∑ i in Finset.univ.filter (fun i => e i∈S),j (e i))=∑ i in S,j i := by
  rw [Finset.sum_filter]
  have h := Fintype.sum_equiv e (fun i : Fin 4 => if e i∈S then j (e i) else 0)
    (fun i : ι => if i∈S then j i else 0) (fun _ => rfl)
  rw [h]
  have hf : Finset.univ.filter (fun i => i∈S)=S := by ext i; simp
  rw [← Finset.sum_filter,hf]

lemma carrierRow_offsets_not_all_zero {N m k : ℕ} (A : Fin m → Point N)
    (β B D : Fin m → ℝ) (F : Fin k → Fin m → ℝ)
    (j : Fin k → ℝ) (flip : Fin k → Bool)
    (hg : ∀ x,0≤preact A β (carrierRow j flip B D F) 0 x)
    (x₀ : Point N) (hD : preact A β D 0 x₀=0) (hB : preact A β B 0 x₀<0) :
    ∃ i,F i≠0 := by
  by_contra hn
  push_neg at hn
  have h := hg x₀
  rw [preact_carrierRow,hD,mul_zero,add_zero] at h
  simp only [hn,preact,Pi.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero,add_zero,sub_zero] at h
  have hp : 0≤preact A β B 0 x₀ := by simpa only [preact,add_zero] using h
  exact (not_lt.mpr hp) hB

/-- The actual atom offset rows are either supported on the two halves of one
code coordinate, or have one common canceled support. The nonzero condition
is supplied by the physical carrier and a negative diagonal probe. -/
theorem network_codeOffsetRow_cases (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hcode : codeDet U≠0)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (e : Fin 4 ≃ NetworkAtoms net) (hnonzero : ∃ i,codeOffsetRow net U (e i)≠0) :
    (∃ (S T : Finset (Fin 4)) (c d : ℝ),
      (∑ i in S,networkAtomJump net (e i))=0 ∧ (∑ i in T,networkAtomJump net (e i))=0 ∧
      (fun i => codeOffsetRow net U (e i))=halflineOffsets positiveRightCodeRow negativeRightCodeRow S T c d) ∨
    (∃ (S T : Finset (Fin 4)) (c d : ℝ),
      (∑ i in S,networkAtomJump net (e i))=0 ∧ (∑ i in T,networkAtomJump net (e i))=0 ∧
      (fun i => codeOffsetRow net U (e i))=halflineOffsets positiveCodeRow negativeCodeRow S T c d) ∨
    (∃ (S : Finset (Fin 4)) (H : Fin 6 → ℝ),
      (∑ i in S,networkAtomJump net (e i))=0 ∧
      ∀ i,codeOffsetRow net U (e i)=if i∈S then H else 0) := by
  classical
  have hind := network_signed_offset_indicators net (by decide) U hU hcode hb hnet
  have hd := network_offset_support_dichotomy net (by decide) U (inverseCode U) hU
    (inverseCode_rightInverse U hcode) hb hnet
  dsimp only at hd
  rcases hd with hleft | hright | ⟨Z,l,n,hZ,hl,hn⟩
  · obtain ⟨S,c,hS,hc⟩ := hind.2 true
    obtain ⟨T,d,hT,hd⟩ := hind.2 false
    let S' := Finset.univ.filter (fun i : Fin 4 => e i∈S)
    let T' := Finset.univ.filter (fun i : Fin 4 => e i∈T)
    left
    refine ⟨S',T',c,d,?_,?_,?_⟩
    · exact (reindex_filtered_sum e S (networkAtomJump net)).trans hS
    · exact (reindex_filtered_sum e T (networkAtomJump net)).trans hT
    · funext i a
      fin_cases a <;> norm_num [codeOffsetRow,halflineOffsets,positiveRightCodeRow,negativeRightCodeRow,
        S',T',hleft,hc,hd]
  · obtain ⟨S,c,hS,hc⟩ := hind.1 true
    obtain ⟨T,d,hT,hd⟩ := hind.1 false
    let S' := Finset.univ.filter (fun i : Fin 4 => e i∈S)
    let T' := Finset.univ.filter (fun i : Fin 4 => e i∈T)
    right
    left
    refine ⟨S',T',c,d,?_,?_,?_⟩
    · exact (reindex_filtered_sum e S (networkAtomJump net)).trans hS
    · exact (reindex_filtered_sum e T (networkAtomJump net)).trans hT
    · funext i a
      fin_cases a <;> norm_num [codeOffsetRow,halflineOffsets,positiveCodeRow,negativeCodeRow,
        S',T',hright,hc,hd]
  · let S : Finset (NetworkAtoms net) := Finset.univ.filter (fun i => i∈Z)
    let S' := Finset.univ.filter (fun i : Fin 4 => e i∈S)
    let H : Fin 6 → ℝ := ![0,0,l true,l false,n true,n false]
    have hrows : ∀ i,codeOffsetRow net U (e i)=if i∈S' then H else 0 := by
      intro i
      by_cases hi : e i∈Z
      · have hm : i∈S' := by simpa [S',S] using hi
        rw [if_pos hm]
        funext a
        fin_cases a <;> norm_num [codeOffsetRow,H,hl,hn,hi]
      · have hm : i∉S' := by simpa [S',S] using hi
        rw [if_neg hm]
        funext a
        fin_cases a <;> norm_num [codeOffsetRow,hl,hn,hi]
    have hcoef : (∃ s,l s≠0) ∨ (∃ s,n s≠0) := by
      by_contra hz
      push_neg at hz
      obtain ⟨i,hi⟩ := hnonzero
      apply hi
      funext a
      fin_cases a <;> norm_num [codeOffsetRow,hl,hn,hz.1,hz.2]
    have hsum : (∑ i in S,networkAtomJump net i)=0 := by
      rcases hcoef with ⟨s,hs⟩ | ⟨s,hs⟩
      · have hbal := actual_offset_separable_balance net U hU hcode hb hnet (if s then 1 else -1) 0
        have hvec : separableOffsets
            (fun s (i : NetworkAtoms net) => offsetLeft net.W₂ (inverseCode U) s i.val)
            (fun s (i : NetworkAtoms net) => offsetRight net.W₂ (inverseCode U) s i.val)
            (if s then 1 else -1) 0=
          (fun i : NetworkAtoms net => offsetLeft net.W₂ (inverseCode U) s i.val) := by
          funext i
          cases s <;> norm_num [separableOffsets,relu]
        rw [hvec] at hbal
        apply indicator_support_zero_sum (networkAtomJump net) _ S (l s) hs hbal
        intro i
        simpa [S] using hl s i
      · have hbal := actual_offset_separable_balance net U hU hcode hb hnet 0 (if s then 1 else -1)
        have hvec : separableOffsets
            (fun s (i : NetworkAtoms net) => offsetLeft net.W₂ (inverseCode U) s i.val)
            (fun s (i : NetworkAtoms net) => offsetRight net.W₂ (inverseCode U) s i.val)
            0 (if s then 1 else -1)=
          (fun i : NetworkAtoms net => offsetRight net.W₂ (inverseCode U) s i.val) := by
          funext i
          cases s <;> norm_num [separableOffsets,relu]
        rw [hvec] at hbal
        apply indicator_support_zero_sum (networkAtomJump net) _ S (n s) hs hbal
        intro i
        simpa [S] using hn s i
    exact Or.inr (Or.inr ⟨S',H,(reindex_filtered_sum e S (networkAtomJump net)).trans hsum,hrows⟩)

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
