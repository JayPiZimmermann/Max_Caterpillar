# Lean count-proof simplification, 25 October 2026

The count proof keeps all existing definitions, theorem names, exact types, constants,
and face-state hypotheses. Four production files lose 114 lines overall. The affected
`MaxCaterpillar.Count.Main` import closure builds, and the six moved or changed
statements pass exact-type checks copied from commit
`e1ebfc0d22ba9097ef0aa0fb322104cca80af660`, with only `propext`, `Classical.choice`,
and `Quot.sound`.

## One quadratic proof

**FACTOR_ESSENTIAL.** The caterpillar and arbitrary-tree three-set counts previously
repeated the same six-point test, uniform parameter choice, covering argument, and
factorial cancellation. The generic `Trees.choose_three_le_of_good` and
`Trees.count_lower_of_good` now live earlier in `CountLower.lean`; their fully
qualified names and types are unchanged. Both caterpillar statements are direct
corollaries through `exists_descr`. `Count/TreeFace.lean` supplies only the tree
model and its bridge to the shared theorem. This removes 100 lines without adding
an import cycle or replacing the general statement by a special case.

A direct corollary of the exponential count was considered and rejected: its
three-set constant is weaker, so it would not preserve the sharp quadratic
statement. Sharing the existing six-point argument retains that constant.

## A uniform block estimate

**DIRECT_REPLACE.** The previous proof of `star_weight_le_one` separately treated
maximum degrees 2, 3, and at least 4, using an estimate for exp(1/2). The replacement
keeps the relation between the coefficient and exponent. Write
$y=1/(2\Delta+2)\leq1/6$, so $\Delta y=1/2-y$. For $2\leq s\leq\Delta$,

$$
\begin{aligned}
(1/2+y)(1+y)^s+y^s/2
&\leq (1/2+y)\bigl[1+(1/2-y)+\tfrac34(1/2-y)^2\bigr]+y^2/2\\
&=27/32+13y/16-7y^2/8+3y^3/4\\
&\leq283/288<1.
\end{aligned}
$$

The first line uses the library's quadratic exponential remainder estimate and
$(1+y)^s\leq\exp(sy)\leq\exp(1/2-y)$. The case $s=1$ is direct. There are no
maximum-degree cases. The old `exp_half_lt` declaration remains available for
compatibility. Final arithmetic uses `linarith only`, since the needed monomial
bounds are already available; a trial with `nlinarith` was stopped after excessive
elaboration and is not needed for the mathematical argument.

## Mixed expansions

**DIRECT_REPLACE (bookkeeping).** In `unified_choose_le`, choose a tree representative
only for each caterpillar occurring in the finite expansion. `choose!` supplies
irrelevant values outside that set, removing a manual global membership split.
The bound, representation identity, and output coefficients are unchanged.

## Evidence and limits

- Build: `lean_count_logs/main_v1.log`, exit 0.
- Exact old statements and axiom checks: `CountSimplificationCheck.lean`,
  `lean_count_logs/exact_check.log`, exit 0.
- Content-bound diagnostic receipt: `lean_count_simplification_receipt.json`.

The receipt checks these working-tree sources. It does not replace the repository's
public clean-closure certificate. This refactor simplifies existing formal bounds;
it does not formalize the newer, stronger written face-capacity estimates.
