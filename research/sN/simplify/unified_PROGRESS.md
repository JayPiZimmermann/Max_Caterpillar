# Unified exponential count -- progress log

## Step 1 (2026-10-24): read-in, new per-unit argument, first numerics
Read exponential.md, coverage.md, Simplify/{BlockSum,StarCover,Reduced,Coverage,CoverageMain}.lean.
Observation: reduced(Delta) is contained in out-leaf(Delta) (out-leaves are non-pendants), so the
union is the out-leaf class; the task is a 2s+2-type base for it.
New argument = reduced-route proof with a *different star cover*: R = {out-leaf -- its neighbour}
u {poor v -- heir(v)}, poor = degree >= 2 without out-leaf/pendant neighbour, heir(v) = child of
an edge at v whose child is not v (injective child map). R-degree <= max(2, omega(v)),
omega(v) = #out-leaf nbrs + [v has a neighbour of degree >= 2]. Free vertices without R-nbr have a
pendant nbr or are fixed leaves (deg 1, kappa not in {0,1}; always tied).
Class: omega <= Delta (contains reduced(Delta) and out-leaf(Delta-1)); base 2 Delta + 2.
unified_proof_check.py (random, n = 5, 6): per-unit lemma and every proof step pass.

## Step 2 (2026-10-24): numerics
unified_exh.c (+ unified_exh.py): exhaustive, all forests n <= 6 up to iso, kappa in {-1..deg+1}:
sum_T y^|T| q(T) <= 1 at y = 1/(2 Delta + 2), Delta = max(2, max omega); max_{m>=3} ratio 0.037.
unified_proof_check.py: every proof step; random n = 5, 6; hill-climb n = 7 (10x150), n = 8 (6x80);
unified_exh_proof.py: exhaustive n <= 5 over all rootings (57 535 instances at n = 5). No failure.

## Step 3 (2026-10-24): Lean done
Simplify/Unified.lean (616): card_passes_le_cover (abstract, R-parametrised copy of
card_passes_le_red), heir construction, card_passes_le_unified.
Simplify/UnifiedMain.lean (232): omegaLe_of_redDeg, omegaLe_of_outLeafBound, unified_choose_le,
unified_exponential (all N >= 3), caterpillar_/brunck_/hingeDeg_/outLeaf_unified_exponential.
Axioms propext/Quot.sound/Classical.choice (UnifiedStatements.lean, unified_statements.log).
Write-up: unified.md.
