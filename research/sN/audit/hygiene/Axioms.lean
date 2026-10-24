import MaxCaterpillar.CountExp
import Lean

open Lean Elab Command

#check @MaxCaterpillar.caterpillar_count_exponential
#check @MaxCaterpillar.caterpillar_count_exponential_pow
#print axioms MaxCaterpillar.caterpillar_count_exponential
#print axioms MaxCaterpillar.caterpillar_count_exponential_pow
#print axioms MaxCaterpillar.CountExp.card_passSet_le
#print axioms MaxCaterpillar.CountExp.exists_passes
#print axioms MaxCaterpillar.CountExp.choose_le_six_pow_mul_card
#print axioms MaxCaterpillar.CountExp.choose_le_six_pow_mul_card'
#print axioms MaxCaterpillar.CountExp.seven_pow_le

/-- Every constant defined in a CountExp module: report any axiom outside the
standard three, and any constant marked unsafe/partial/extern/implemented_by. -/
elab "#audit_countexp" : command => do
  let env ← getEnv
  let some idx0 := env.getModuleIdx? `MaxCaterpillar.CountExp | throwError "no module"
  let mods := #[`MaxCaterpillar.CountExp, `MaxCaterpillar.CountExp.Defs,
    `MaxCaterpillar.CountExp.W1Functional, `MaxCaterpillar.CountExp.W2Digits,
    `MaxCaterpillar.CountExp.W3Structure, `MaxCaterpillar.CountExp.W4Orders,
    `MaxCaterpillar.CountExp.W5Generating, `MaxCaterpillar.CountExp.Main]
  let _ := idx0
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut bad : Array String := #[]
  for m in mods do
    let some idx := env.getModuleIdx? m | throwError s!"missing {m}"
    for c in env.header.moduleData[idx.toNat]!.constNames do
      n := n + 1
      let cs := toString c
      if ["_cstage", "_spec", "_closed", "_elambda", "_lambda", "_boxed", "_rarg", "._at."].any (fun t => (cs.splitOn t).length > 1) then continue
      let some ci := env.find? c | continue
      if ci.isUnsafe || ci.isPartial then bad := bad.push s!"unsafe/partial: {c}"
      if ci matches .axiomInfo _ then bad := bad.push s!"axiom decl: {c}"
      if ci matches .opaqueInfo _ then bad := bad.push s!"opaque decl: {c}"
      if (Compiler.getImplementedBy? env c).isSome then bad := bad.push s!"implemented_by: {c}"
      let ((), st) := ((CollectAxioms.collect c).run env).run {}
      let axs := st.axioms
      for a in axs do
        unless ok.contains a do bad := bad.push s!"{c} uses {a}"
  logInfo m!"checked {n} constants; problems: {bad}"

#audit_countexp
