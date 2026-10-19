# Provenance and attribution

This repository contains the Lean formalization and paper for the caterpillar
construction of a two-hidden-layer ReLU network representing
$\operatorname{MAX}_N$. It intentionally excludes the Lean development of the
general result for arbitrary continuous piecewise affine functions and excludes
unrelated archived constructions.

The geometric route is based on the Brunck--Stade--Yehudayoff construction,
including the use of support functions, exposed faces, and lower-dimensional
corrections. The accompanying paper cites their work and states precisely how
the caterpillar specialization for the maximum follows and where its proof uses
the same geometric ideas. Retaining the required geometric Lean dependencies
does not claim independent authorship of that machinery.

Jakob Paul Zimmermann is the author of this Lean repository and accompanying
manuscript, which develop the maximum specialization, its explicit caterpillar
formula, and its width reduction. Claude Code and Codex assisted with Lean
proof search, formalization, checking, and manuscript preparation.

The ICLR layout, the Lean-reference commands, and the two supplied style files
come from the arXiv v2 source of
[*Removing spurious minima for planar features by skip connections*](https://arxiv.org/abs/2610.01728).
Their use is documented in [paper/README.md](paper/README.md).

No upstream project license was present in the source snapshot. This repository
does not infer a new license for inherited material. Third-party Lean
dependencies retain their own licenses and are fetched separately.
