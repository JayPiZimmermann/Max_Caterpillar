import MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.UnitAttachment
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.Ordering

/-! # Raw exceptional switching orientations attach by their derived actual baseline -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment

lemma exceptionalFlags_of_equal_ne : ∀ b₀ b₁ b₂ : Bool,
    b₀=b₁ → b₀≠b₂ → ThreeExceptional.ExceptionalFlags b₀ b₁ b₂ := by
  unfold ThreeExceptional.ExceptionalFlags
  decide

/-- The exceptional flags are only a finite case of the already derived raw
three-atom classification. Both arbitrary spectator outputs are classified
and normalized inside the actual exceptional-profile theorem. -/
theorem exceptional_switching_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U≠0)
    (hW : a.val.W₁=pairedRows U) (hb : a.val.HasZeroBiases)
    (e : Fin 3 ≃ NetworkAtoms a.val)
    (hj : ∀ i,networkAtomJump a.val (e i)=(![1,1,-1] : Fin 3 → ℝ) i)
    (hoff : ∀ u v,networkAtomOffset a.val U u v (e 0)*networkAtomOffset a.val U u v (e 1)=0 ∧
      networkAtomOffset a.val U u v (e 2)=
        networkAtomOffset a.val U u v (e 0)+networkAtomOffset a.val U u v (e 1))
    (hsame : networkAtomFlip a.val (e 0)=networkAtomFlip a.val (e 1))
    (hne : networkAtomFlip a.val (e 0)≠networkAtomFlip a.val (e 2)) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  obtain ⟨q,hprofile,_,hraw⟩ := network_switching_profile a.val U hdet hW hb a.property e hj hoff
  let F := atomOffsetRow a.val U (e 0)
  let G := atomOffsetRow a.val U (e 1)
  let rows := switchingProfileRows a.val U e q
  let weights := switchingProfileWeights a.val q
  have hsource : ∀ x,(ThreeExceptional.profileNet U F G rows weights
      (networkAtomFlip a.val (e 0)) (networkAtomFlip a.val (e 1))
      (networkAtomFlip a.val (e 2))).eval x=Maximum 4 x := hprofile
  have hF := atomOffsetRow_comparison_zero a.val U (e 0)
  have hG := atomOffsetRow_comparison_zero a.val U (e 1)
  obtain ⟨n,hnpath,hnW,hnb,hnout,hnrow⟩ := ThreeExceptional.exceptional_profile_to_unit_fiber
    U hdet F G rows weights (networkAtomFlip a.val (e 0)) (networkAtomFlip a.val (e 1))
    (networkAtomFlip a.val (e 2))
    (exceptionalFlags_of_equal_ne _ _ _ hsame hne) hF.1 hF.2 hG.1 hG.2
    (switchingProfile_disjoint a.val U hdet e hoff) hsource
  have hunit := literal_unit_quotient_joined n U hdet hnW hnb 0
    (networkAtomFlip a.val (e 0)) hnout hnrow
  have hmiddle := joinedIn_exact_quotient
    (⟨ThreeExceptional.profileNet U F G rows weights (networkAtomFlip a.val (e 0))
      (networkAtomFlip a.val (e 1)) (networkAtomFlip a.val (e 2)),hsource⟩ : ExactFiber 4 6 5)
    n hnpath
  exact hraw.trans (hmiddle.trans hunit)

#print axioms exceptional_switching_quotient_joined
end MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
