import MaxCaterpillar.Frontier.StarCertificate.XiMasks

/-! The displayed mask records exactly the leaves preceding the centre.
This fixed finite ordering fact contains no certificate coefficient claim. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MaxCaterpillar.Frontier.StarCertificate

theorem table_leavesBeforeCenter : ∀ (p : Fin 120) (i : Fin 4),
    Nat.testBit (centerBeforeMask p).val i.val=true ↔
      ∃ a b : Fin 5, a.val<b.val ∧ permutationTable p a=i.castSucc ∧
        permutationTable p b=4 := by decide

#print axioms table_leavesBeforeCenter
end MaxCaterpillar.Frontier.StarCertificate
