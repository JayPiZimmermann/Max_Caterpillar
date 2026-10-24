# Cleanup pass: one (shortest) route per result

## Checkpoint status, 24 October 2026

This is an unfinished source consolidation, preserved at the user's request.
The count proof is now in `MaxCaterpillar/Count/`, the dimension proof in
`MaxCaterpillar/Dimension.lean`, and rationality uses the projection lemma.
The old 122-statement certificate is historical. Its manifest still names
removed declarations and must be reconciled before a new public verification
claim. `logs/build1.log` is a failed earlier build; `logs/commit_build.log`
records the interrupted fresh checkpoint build (tool exit 143 while rebuilding
generated Max5Lns27 cells). No successful full build or new axiom audit is
claimed. A narrower public-interface build is recorded in
`logs/commit_interface_build.log`: `lake build MaxCaterpillar.Theorems`
passed with exit 0. This verifies its build closure, not the stale public
manifest or all generated small-arity certificates.
The paper's 175 supporting declaration links resolve against the current
sources. Research certificates and numerical probes have separate statuses
in their own ledgers.

The snapshot excludes local Python virtual environments, compiled research
executables, interrupted `_tmp_*.bin` / grading `.in` matrices, and the
large `trees/logs/l2A_*.npy` evaluation cache. They remain on disk. The
C/C++ sources and matrix producers (`dfs/h3-grading/{sym,ysym2,young7}.py`
and `trees/twin_l2.py`) are included. Other nonignored research artifacts
are preserved, including the exact Fourier certificates.

## Original cleanup plan

Baseline: commit a503f01 (122 certified statements), MaxCaterpillar/ = 57062 lines (incl. generated SmallN cells).

## Steps
- [ ] 1. Declaration-level dependency analysis (research/sN/cleanup/Deps.lean)
- [ ] 2. Rationality: projection lemma only; caterpillar_net direct; delete V1-V3 routes
- [ ] 3. Exponential count: unified route only; delete CountExp, Trees/{BoundedDegree,Hubs,Combined}, Simplify/{Coverage,...}
- [ ] 4. Dimension: delete LowerBound.lean
- [ ] 5. Manifest + verify
- [ ] 6. Paper + announcement
