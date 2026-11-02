import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.Normalization
import MaxCaterpillar.Fiber.Count65.Paired.CodeOffsets

/-! # Zero-sum indicator supports extracted from actual four-atom completions -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier
variable {m : ℕ}

/-- Every four-atom coefficient vector has a zero-sum indicator support,
including the identically zero vector. -/
theorem indicator_zero_sum_of_four_atoms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j f : ι → ℝ) (hj : ∀ i,j i≠0) (hcard : Fintype.card ι≤4)
    (hbal : Paired65.AtomBalance j f) :
    ∃ (S : Finset ι) (c : ℝ),(∑ i in S,j i)=0 ∧
      ∀ i,f i=if i∈S then c else 0 := by
  classical
  by_cases hz : ∀ i,f i=0
  · exact ⟨∅,0,by simp,by simpa using hz⟩
  · push_neg at hz
    obtain ⟨i,hi⟩ := hz
    let S := Finset.univ.filter (fun i => f i≠0)
    have hone := oneLevel_of_atomBalance j f hj hbal hcard
    have hrepr : ∀ a,f a=if a∈S then f i else 0 := by
      intro a
      simpa [S,Function.mem_support] using oneLevel_indicator f hone i hi a
    exact ⟨S,f i,indicator_support_zero_sum j f S (f i) hi hbal hrepr,hrepr⟩

lemma actual_offset_separable_balance (net : Network 4 6 m)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U)
    (hcode : codeDet U≠0) (hb : net.HasZeroBiases)
    (hnet : ∀ x,net.eval x=Maximum 4 x) (u v : ℝ) :
    Paired65.AtomBalance (networkAtomJump net)
      (separableOffsets
        (fun s (i : NetworkAtoms net) => offsetLeft net.W₂ (inverseCode U) s i.val)
        (fun s (i : NetworkAtoms net) => offsetRight net.W₂ (inverseCode U) s i.val) u v) := by
  have hbal := network_effective_atomBalance net U hU hb hnet
    (inverseCode U 0 0*u+inverseCode U 0 1*v)
    (inverseCode U 1 0*u+inverseCode U 1 1*v)
  have hoff : ∀ i : NetworkAtoms net,
      separableOffsets
        (fun s (i : NetworkAtoms net) => offsetLeft net.W₂ (inverseCode U) s i.val)
        (fun s (i : NetworkAtoms net) => offsetRight net.W₂ (inverseCode U) s i.val) u v i=
        networkAtomOffset net U (inverseCode U 0 0*u+inverseCode U 0 1*v)
          (inverseCode U 1 0*u+inverseCode U 1 1*v) i := by
    intro i
    exact physical_offset_separable net.W₂ U (inverseCode U) (inverseCode_rightInverse U hcode)
      i.val (networkAtom_comparison_ne_zero net i) u v
  exact (congrArg (Paired65.AtomBalance (networkAtomJump net)) (funext hoff)).mpr hbal

/-- Every signed-coordinate coefficient vector of an actual exact paired
completion with at most four effective atoms is a canceled indicator group. -/
theorem network_signed_offset_indicators (net : Network 4 6 m) (hm : m≤5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U)
    (hcode : codeDet U≠0) (hb : net.HasZeroBiases)
    (hnet : ∀ x,net.eval x=Maximum 4 x) :
    (∀ s : Bool,∃ (S : Finset (NetworkAtoms net)) (c : ℝ),
      (∑ i in S,networkAtomJump net i)=0 ∧
      ∀ i,offsetLeft net.W₂ (inverseCode U) s i.val=if i∈S then c else 0) ∧
    (∀ s : Bool,∃ (S : Finset (NetworkAtoms net)) (c : ℝ),
      (∑ i in S,networkAtomJump net i)=0 ∧
      ∀ i,offsetRight net.W₂ (inverseCode U) s i.val=if i∈S then c else 0) := by
  classical
  have hj : ∀ i : NetworkAtoms net,networkAtomJump net i≠0 := fun i => i.property
  have hc := effectiveAtoms_card_le_four 0 0 net.w₃ (codeIntercept net.W₂ U 0 0)
    (fun i => net.W₂ i 0) (fun i => net.W₂ i 1) hm
    (network_two_increment_identity net U hU hb hnet 0 0)
  constructor
  · intro s
    have hbal := actual_offset_separable_balance net U hU hcode hb hnet (if s then 1 else -1) 0
    have he : separableOffsets
        (fun s (i : NetworkAtoms net) => offsetLeft net.W₂ (inverseCode U) s i.val)
        (fun s (i : NetworkAtoms net) => offsetRight net.W₂ (inverseCode U) s i.val)
        (if s then 1 else -1) 0=
      (fun i : NetworkAtoms net => offsetLeft net.W₂ (inverseCode U) s i.val) := by
      funext i
      cases s <;> norm_num [separableOffsets,relu]
    rw [he] at hbal
    exact indicator_zero_sum_of_four_atoms (networkAtomJump net) _ hj hc hbal
  · intro s
    have hbal := actual_offset_separable_balance net U hU hcode hb hnet 0 (if s then 1 else -1)
    have he : separableOffsets
        (fun s (i : NetworkAtoms net) => offsetLeft net.W₂ (inverseCode U) s i.val)
        (fun s (i : NetworkAtoms net) => offsetRight net.W₂ (inverseCode U) s i.val)
        0 (if s then 1 else -1)=
      (fun i : NetworkAtoms net => offsetRight net.W₂ (inverseCode U) s i.val) := by
      funext i
      cases s <;> norm_num [separableOffsets,relu]
    rw [he] at hbal
    exact indicator_zero_sum_of_four_atoms (networkAtomJump net) _ hj hc hbal

/-- The physical row containing precisely the four signed code coefficients
of the extracted scalar atom offset. -/
noncomputable def codeOffsetRow (net : Network 4 6 m) (U : Fin 2 → Fin 2 → ℝ)
    (i : NetworkAtoms net) : Fin 6 → ℝ :=
  ![0,0,offsetLeft net.W₂ (inverseCode U) true i.val,
    offsetLeft net.W₂ (inverseCode U) false i.val,
    offsetRight net.W₂ (inverseCode U) true i.val,
    offsetRight net.W₂ (inverseCode U) false i.val]

lemma codeOffsetRow_form (net : Network 4 6 m) (U : Fin 2 → Fin 2 → ℝ)
    (hcode : codeDet U≠0) (i : NetworkAtoms net) (x : Point 4) :
    endpointForm U (codeOffsetRow net U i) x=networkAtomOffset net U (x 1) (x 3) i := by
  have hoff := physical_offset_separable net.W₂ U (inverseCode U) (inverseCode_rightInverse U hcode)
    i.val (networkAtom_comparison_ne_zero net i) (anchorCodeValue U x 0) (anchorCodeValue U x 1)
  have ha := (inverseCode_anchor_eval U hcode (x 1) (x 3)).1
  have hb := (inverseCode_anchor_eval U hcode (x 1) (x 3)).2
  change inverseCode U 0 0*anchorCodeValue U x 0+
    inverseCode U 0 1*anchorCodeValue U x 1=x 1 at ha
  change inverseCode U 1 0*anchorCodeValue U x 0+
    inverseCode U 1 1*anchorCodeValue U x 1=x 3 at hb
  rw [ha,hb] at hoff
  rw [endpointForm,endpointFeature_eq]
  norm_num [codeOffsetRow,Fin.sum_univ_succ]
  simpa only [separableOffsets,networkAtomOffset,add_assoc] using hoff

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
