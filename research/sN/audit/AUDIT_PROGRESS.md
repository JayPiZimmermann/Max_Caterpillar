# Semantic audit of public claims — progress log

## Step 0 (start)
- Read conventions/build skills, Definitions/Theorems/Core/OneBasis/Quotient, Trees/*, Frontier/*.
- Plan: new files MaxCaterpillar/Audit/{Nonvacuity,CaterpillarTree,Widths}.lean + MaxCaterpillar/Audit.lean.
- Finding: maxFourNet (6,3) has TWO positive-sum rows (x1, x3) and two negative rows, so it does
  NOT witness second_width_half_succ; maxThreeNet (4,3) does (rows sum 0,0,1,-1).

## Step 1 (files written)
- MaxCaterpillar/Audit/Expansion.lean: `Audit.exists_isCaterpillarExpansion` (compiled OK).
  Name `exists_caterpillarExpansion` already exists in Sharing.lean (PairExpansion version), so
  the new names carry the `is` prefix.
- MaxCaterpillar/Audit/CaterpillarTree.lean: `TreeFace.IsCaterpillar`, bridge
  `Audit.caterpillarFunction_eq_treeFace`, tree/rooted-star/mixed nonvacuity (compiling).
- MaxCaterpillar/Audit/Widths.lean: witnesses N=3 (maxThreeNet), N=4 (new maxFourNetOne) for
  second_width_half_succ; second_width_joint hypothesis false for N=3,4; free_neurons witness.
- Docstring of second_width_joint (Frontier/GeneralN2.lean) marked conditional.

## Step 2 (all three audit files compile; `lake env lean` exit 0)
- Audit/Expansion.lean, Audit/CaterpillarTree.lean, Audit/Widths.lean OK. Root import added.

## Step 3
- Root `lake build MaxCaterpillar` OK with Audit imported; CheckAll.lean (#check @ all 112 claims +
  new ones, log research/sN/audit/CheckAll.log): no auto-bound surprises; new theorems use only
  propext/Classical.choice/Quot.sound.
- Added Audit/TreeHyps.lean: hingeDeg ≤ N, OutLeafBound D N, exists_isTreeExpansion_bounded,
  generic transfer `isTreeExpansion_of_pred` (gives RedDeg-2 nonvacuity together with
  Simplify.caterpillarFunction_eq_upTree + redDeg_of_isUpCaterpillar, uncommitted files of
  another agent, so not imported here).
- Next: append claims to main.json, run verify.

## Step 4 (final)
- Appended 10 claims (main.json now 122; my two others were appended by the coordinator).
- `scripts/lean_lock.sh python3 scripts/verify.py`: PASS: 122 exact statements; 303 Lean files;
  only permitted axioms (log research/sN/audit/verify_audit.log).
