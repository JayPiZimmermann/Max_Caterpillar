# Second overnight checkpoint inventory

The inventory selects thirteen frozen receipts: the actual cycle/forest
equivalence and star-only H(5,2) proof; quadratic constants and unrestricted
total/feeding tradeoffs through denominator 175,000; the support-transversal
and coordinate-quotient bridges; the sharp conditional feeding/support
tradeoff; and the degree-two graph bound.

`selection.json` binds 1,994 files, including all discovered project imports,
reproducibility controls, and receipt-bound logs. All hashes match. Of these,
520 files are new relative to commit 7bac92a; 1,474 already match the public
worktree. No existing receipt-bound publication file needs replacement.
The independent source scan checks 1,575 Lean files and finds no forbidden
constructs. Each theorem's kernel/type/nonvacuity evidence comes from its
specified receipt; the inventory itself does not rerun Lean or promote a
research module into the production root.

The parent completed the final selection after the parallel workers reached
their service usage limit. At that point the degree-two and 175,000 constant
gates had already finished successfully. Their final receipts, rather than
earlier progress messages, determine the selected scope.

The original working tree contains other unfinished or separately verified
branches. They are excluded unless imported by this precise closure. In
particular, the new signed-gradient concentration and near-exponential
network wrappers are a separate checkpoint, not silently included here.

Reproduce this read-only inventory with `python3
research/sN/overnight_20261103/checkpoint_002/inventory.py` in the original
research checkout. Its comparison worktree path is explicit in the script.
Use each individual receipt's command to rebuild that theorem's evidence.

The exact theorem types and model distinctions were independently reviewed
in `claims_audit.md` and by the theorem-specific drivers. In particular,
total first width and feeding first width are not interchangeable when
comparing numerical constants.
