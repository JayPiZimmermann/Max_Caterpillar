import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.Ordinary
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.Profile

/-! # The ordinary switching alternative of a raw physical network reaches a unit gate -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
open Absorption

theorem raw_ordinary_switching_to_unit (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U≠0) (hW : net.W₁=pairedRows U)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (e : Fin 3 ≃ NetworkAtoms net)
    (hj : ∀ i,networkAtomJump net (e i)=(![1,1,-1] : Fin 3 → ℝ) i)
    (hoff : ∀ a b,networkAtomOffset net U a b (e 0)*networkAtomOffset net U a b (e 1)=0 ∧
      networkAtomOffset net U a b (e 2)=
        networkAtomOffset net U a b (e 0)+networkAtomOffset net U a b (e 1))
    (hflip : networkAtomFlip net (e 0)=networkAtomFlip net (e 2)) :
    ∃ n : ExactFiber 4 6 5,n.val.W₁=pairedRows U ∧ n.val.HasZeroBiases ∧
      n.val.w₃ 0=1 ∧
      n.val.W₂ 0=(if networkAtomFlip net (e 0) then -comparisonRow U else comparisonRow U) ∧
      Joined (quotientMk (⟨net,hnet⟩ : ExactFiber 4 6 5)) (quotientMk n) := by
  obtain ⟨q,hprofile,_,hraw⟩ := network_switching_profile net U hdet hW hb hnet e hj hoff
  let F := atomOffsetRow net U (e 0)
  let G := atomOffsetRow net U (e 1)
  let rows := switchingProfileRows net U e q
  let weights := switchingProfileWeights net q
  have he : switchingProfile net U e q=
      literalSwitching U F G (networkAtomFlip net (e 0)) (networkAtomFlip net (e 1))
        (networkAtomFlip net (e 0)) rows weights 0 := by
    unfold switchingProfile literalSwitching
    rw [hflip]
  have hsource : ∀ x,(literalSwitching U F G (networkAtomFlip net (e 0))
      (networkAtomFlip net (e 1)) (networkAtomFlip net (e 0)) rows weights 0).eval x=Maximum 4 x := by
    rw [← he]
    exact hprofile
  obtain ⟨n,hnW,hnb,hnout,hnrow,hnpath⟩ := literalSwitching_ordinary_to_unit U F G
    (networkAtomFlip net (e 0)) (networkAtomFlip net (e 1)) rows weights
    (switchingProfile_disjoint net U hdet e hoff) hsource
  have hepoint : (⟨switchingProfile net U e q,hprofile⟩ : ExactFiber 4 6 5)=
      ⟨literalSwitching U F G (networkAtomFlip net (e 0)) (networkAtomFlip net (e 1))
        (networkAtomFlip net (e 0)) rows weights 0,hsource⟩ := Subtype.ext he
  rw [hepoint] at hraw
  exact ⟨n,hnW,hnb,hnout,hnrow,hraw.trans (joinedIn_exact_quotient _ n hnpath)⟩

#print axioms raw_ordinary_switching_to_unit
end MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
