import Lean.Elab.Tactic

/-! # Submit closed Boolean reflexivity directly to the kernel

This elaborator performs no computation and asserts no fact. It proposes the
ordinary proof term `Eq.refl true`. Lean's kernel must check that the goal's
Boolean expression reduces to true; false checks are rejected. Avoiding the
elaborator's duplicate reduction matters for large finite certificates.
-/
namespace MaxCaterpillar.Frontier.StarCertificate
open Lean Elab Tactic Meta

elab "kernel_bool_check" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``Eq 3 && (target.getArg! 0).isConstOf ``Bool &&
      (target.getArg! 2).isConstOf ``Bool.true do
    throwError "kernel_bool_check expects a Boolean equality with true on the right"
  let proof ← mkEqRefl (mkConst ``Bool.true)
  goal.assign proof
  replaceMainGoal []

end MaxCaterpillar.Frontier.StarCertificate
