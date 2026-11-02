import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Coverage
import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Fiber

/-! # Actual star chart coverage through genuine physical symmetries

Only actual positive second-neuron scaling and the original hidden permutation
are used. The zero-bias hypothesis is explicit; arbitrary biases are handled by
the separately proved bias deformation retraction on the global quotient.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
open MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65
open MaxCaterpillar.Fiber.Count65.PhysicalExtraction

lemma zeroBias_eq_of_hasZeroBiases {net : Network 4 6 5} (h : net.HasZeroBiases) :
    net.zeroBias=net := by
  rcases net with ⟨W₁,b₁,W₂,b₂,w₃,b₃⟩
  change b₁=0 ∧ b₂=0 ∧ b₃=0 at h
  rcases h with ⟨rfl,rfl,rfl⟩
  rfl

lemma normalizeSecond_hasZeroBiases {net : Network 4 6 5} (h : net.HasZeroBiases) :
    (normalizeSecond net).HasZeroBiases := by
  rcases h with ⟨h₁,h₂,h₃⟩
  refine ⟨h₁,?_,h₃⟩
  funext k
  change |net.w₃ k| * net.b₂ k=0
  rw [h₂]
  simp

/-- Every exact zero-bias physical star completion lies in a canonical chart
image in the genuine symmetry quotient. Equal network functions alone do not
supply any symmetry step in this proof. -/
theorem zeroBias_quotient_covered (net : ExactFiber 4 6 5) (r : ℝ)
    (hr : 0<r) (hr1 : r≤1) (hz : net.val.HasZeroBiases)
    (hW : net.val.W₁=firstRows r) :
    (∃ o : Fin 3→Bool,∃ p : BranchIFiber o,quotientMk net=branchIQuotient o p) ∨
    (∃ o : Fin 3→Bool,∃ p : BranchIIFiber o,quotientMk net=branchIIQuotient o p) := by
  classical
  have hout := (physical_output_sign_counts net.val r hr hr1 hW net.property).2.2
  obtain ⟨F⟩ := exists_physical_normal_form net.val r hr hr1 hW net.property
  let scaled : ExactFiber 4 6 5 :=
    scaleSecondFiber (fun k => |net.val.w₃ k|) (fun k => abs_pos.mpr (hout k)) net
  let ordered : ExactFiber 4 6 5 :=
    permuteHiddenFiber (Equiv.refl _) (normalFormPermutation F) scaled
  have hzero : (normalizeSecond net.val).zeroBias=normalizeSecond net.val :=
    zeroBias_eq_of_hasZeroBiases (normalizeSecond_hasZeroBiases hz)
  have hval : ordered.val=orderedPhysicalNet F := by
    change permuteHidden (normalizeSecond net.val) (Equiv.refl _) (normalFormPermutation F)=
      permuteHidden (normalizeSecond net.val).zeroBias (Equiv.refl _) (normalFormPermutation F)
    rw [hzero]
  have hquot : quotientMk net=quotientMk ordered :=
    (quotientMk_eq_of_step (SymmetryStep.second net (fun k => |net.val.w₃ k|)
      (fun k => abs_pos.mpr (hout k)))).trans
      (quotientMk_eq_of_step (SymmetryStep.hidden scaled (Equiv.refl _) (normalFormPermutation F)))
  have hfirst : (normalizeSecond net.val).W₁=firstRows r := hW
  rcases physical_normal_form_covered F hr hr1 hfirst with ⟨p,hp⟩ | ⟨p,hp⟩
  · have he : ordered=branchIExact (coreOrientation F) p :=
      Subtype.ext (hval.trans hp.symm)
    refine Or.inl ⟨coreOrientation F,p,?_⟩
    simpa only [he,branchIQuotient] using hquot
  · have he : ordered=branchIIExact (coreOrientation F) p :=
      Subtype.ext (hval.trans hp.symm)
    refine Or.inr ⟨coreOrientation F,p,?_⟩
    simpa only [he,branchIIQuotient] using hquot
end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
