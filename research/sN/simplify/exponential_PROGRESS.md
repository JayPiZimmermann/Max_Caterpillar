# Simplified exponential bound: progress log

## Step 1 (read-in, 2026-10-24)
Read paper app:lower, NOTE.md MAIN ROUTE, trees/PROGRESS.md, CountExp/*, Trees/{DescrPass,
BoundedDegree*,Hubs*,Combined,RootedStars}.lean.
Observations:
- The paper's per-unit count uses only the *shape* of the hinge graph: components = a spine path
  plus pendant vertices with kappa = 0. Rooted stars and ALL their faces (each leaf omitted /
  linear / hinge) have this shape (spine = the root c, pendants = hinge leaves). So no separate
  star argument (and no "omitted-leaf faces are caterpillar faces" check) is needed.
- Simpler per-unit bound found: cut every spine into blocks of 2 vertices (one block of 3 if
  the length is odd >= 3; a lone spine vertex is a block together with one pendant edge).
  Choose one hinge edge outside T per block when possible -> matching; the weight
  sum over spine parts factorises over blocks: pair 1/2+2y+y^2, triple 1/2+2y+3y^2+y^3,
  single 1/2+y; all <= 1 at y = 1/6. Same constant 6 as the paper, no potential function.
  With the exact count 2/6 for a 3-vertex path, y = 1/5 works (base 5).

## Step 2 (unified theorem, human proof written)
- exponential.md: ONE theorem. Pendant = hinge-degree-1 vertex with kappa = 0; reduced forest
  F° = F minus pendants. If every unit's hinge graph is a forest with F° of max degree <= Delta
  (Delta >= 2): C(N,m) <= (2Delta+2)^m |K|. Delta = 2: caterpillars + rooted stars + all their
  faces, all counted, base 6 (same constant as before). Bounded hinge degree: 2Delta+2
  (old 2(12Delta-6)). Blocks = star cover of F° (minimal edge cover) + lone vertices with a
  pendant edge; weight (1/2+y)(1+y)^s + y^s/2 <= 1 at y = 1/(2Delta+2).
- Base-5 remark for Delta = 2 (exact 2/6 for a 3-path block); not in Lean.
- check_shape.py: star faces exact mixed differences N=4,5; random/adversarial shape units N<=7.
- Lean: CatShape.lean (reuse of CountExp per-unit bound, Delta=2 only) queued; new route files
  StarCover.lean (star cover existence), BlockSum.lean (factorisation + weight inequality) written,
  compiling; next: Reduced.lean (per-unit count for RedDeg), Units.lean (instances).

## Step 3 (Lean, new route, in progress)
Files (MaxCaterpillar/Simplify/): StarCover.lean (min edge cover -> star cover), BlockSum.lean
(factorisation over blocks, star weight <= 1 via e^(1/2) < 33/20), Reduced.lean (IsPend, RAdj,
RedDeg, forced vertices, card_passes_le_red), TreeUnits.lean (choose_le_of_red,
pow_le_of_choose_le, seven_pow_le_of_choose_le', TreeFace instances: IsStarFace,
IsUpCaterpillar, hinge degree; tree_reduced_choose_le / _exponential / _exponential_two),
Brunck.lean (caterpillar keys = up-caterpillar tree faces via Audit.treeFaceOf;
IsBrunckExpansion, brunck_expansion_choose_le / _exponential, all units counted, base 6).
CatShape.lean (reuse of old route) deleted: superseded, and its nlinarith hung 30 min.
Lean lock heavily contended (other agents); builds queued.

## Step 4 (Lean complete)
- All five files build; no sorry; axioms propext/Quot.sound/Classical.choice.
- Lines: StarCover 174, BlockSum 202, Reduced 517, TreeUnits 396, Brunck 153 (total 1442).
- Out-leaf theorem (coverage agent) compared in exponential.md: classes incomparable;
  on the common part base 2Δ+2 here vs 16(s+1)/3; subsumption not achieved.
