# Coverage (largest tree class for the exponential bound) -- progress log

## Step 1 (2026-10-24): read-in + new proof idea + numerical check
Read trees/PROGRESS.md, NOTE.md, Trees/{BoundedDegree*,Hubs*,Combined,DescrPass,Quadratic}.lean.
New per-unit argument (no hubs, no degree bound). Abstract setting: hinge forest F, integer kappa.
Only hypothesis: every vertex is adjacent to at most s OUT-LEAVES (F-leaves with kappa = 1).
 L1  T is determined by X = T cap H, H = {kappa >= 1}: for kappa_v <= 0,
     v in T  <=>  kappa_v != 0 or v has a neighbour w with (kappa_w <= 0 or w in T).
 L2  |H \ T| <= (s+1)(|T| + |Y|), Y = untied vertices with an untied hinge child
     (untied u in H: has untied child [in Y] / has tied child [<= |T|, injective] /
      else u is an out-leaf of its parent p, p in T or p in Y [<= s(|T|+|Y|)]).
 L3  |Y| <= 2 nu (chosen child edges have degree <= 2; forest matching lemma |E| <= Delta |P|).
 => 2^-nu <= beta^(|H|-|X|-(s+1)|T|), beta = 1 - 1/(4(s+1)) (beta^(2(s+1)) >= 1/2);
    sum_X beta^(|H|-|X|) (1-beta)^|X| = 1  =>  per unit #passes <= (16(s+1)/3)^k k!(N-k)!.
Numerics (coverage_check.py, coverage_climb.py, n <= 7, random + hill-climb): L1, L2 and the bound
hold in every instance; worst observed bases ~1.4 (s=0), 2.5 (s=1), 2.8 (s=2), 3.2 (s=3).
Next: Lean in MaxCaterpillar/Simplify/Coverage.lean.

## Step 2 (2026-10-24): Lean done
Simplify/Coverage.lean (654 lines) + Simplify/CoverageMain.lean (285 lines) build.
Public: tree_outLeaf_choose_le, tree_outLeaf_exponential, mixed_outLeaf_choose_le,
mixed_outLeaf_exponential, outLeafBound_of_hubOK, outLeafBound_of_hingeDeg_le,
starFace_outLeafBound; axioms propext/Quot.sound/Classical.choice (CoverageStatements.lean,
coverage_statements.log). Not appended to verification/main.json: the root does not import
the files (not allowed to edit existing files); entries ready in coverage_claims.json.
Write-up: coverage.md (statement, proof, uncovered example, adversarial self-check).
