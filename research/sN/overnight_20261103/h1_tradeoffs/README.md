# Relaxing the first hidden width assumption

The main progress here is replacing a total-width cap by the original
feeding width, distinct support sets, and support-sensitive costs. The
conditional exponential theorems retain the displayed structural matching
obstruction H. The unconditional weighted polynomial theorem is maintained
separately in `unconditional/PowerTradeoff.lean`.

## Explicit arbitrary-width conditional bound

Let n=floor(N/2), and let F be the number of original first-hidden neurons
with a nonzero outgoing coefficient into the second hidden layer. Set

    d = 1 + Nat.sqrt (floor(105 F / (16 n²))),
    q = floor(sqrt(n)/(8000 d)).

The actual Lean definition uses `Nat.sqrt` for the integer square root.
If n≥10¹⁰ d² and H(4q+1,q), every exact MAX_N network in the original
nine-array affine-skip model satisfies

    h₂ ≥ exp(3 sqrt(n)/(8000 d))/2.

`SharpTradeoff.lean` proves this without any cap on total h₁. Both original
hidden-layer indices survive every reduction. Biases, linear skips, arbitrary
real first covectors, and signed output coefficients are allowed. Output-only
first neurons are uncharged.

In particular, for F≤C N², set s=ceil(sqrt(C)) (integer C≥1). At
n≥10¹⁰(6s)², and the corresponding H premise, the explicit conclusion is

    h₂ ≥ exp(3 sqrt(n)/(48000 s))/2.

The published predecessor used denominator 160000 C and required a bound
on the total first hidden width. Thus the dependence on C improves from C
to sqrt(C), while the constant also improves. The H premise changes with
the new matching order; this is not a way to infer a stronger bound from
one previously assumed fixed-order H statement.

For F=N^(2+epsilon), 0<epsilon<1, the exponent has order
N^((1-epsilon)/2), conditional on the required growing H. More generally,
the exponent has order min(sqrt(N),N^(3/2)/sqrt(F)). The explicit size
condition permits a small-constant cubic-width regime. A diverging exponent
requires F=o(N³); a superpolynomial conclusion requires the stronger
F=o(N³/log²N). At F proportional to N³ this argument gives only a constant
exponent. These asymptotic interpretations are mathematical consequences
of the exact finite theorem, not separate Lean asymptotic declarations.

## A stronger support-sensitive conditional theorem

For each original first row, let r be its number of nonzero coordinates.
Define

    w(r) = 0                    if r≤2,
           1                    if r=3,
           r(r-1)(r-2)(r-3)    if r≥4.

Charge a row only if its original bias is zero, its coordinate sum is zero,
it feeds some original second neuron, and r≤n. Let

    W = sum of w(r)/2^r over those original rows.

`WeightedTradeoff.conditional_affine_support_tradeoff` needs only
W≤d²n², n≥10¹⁰d², and H at q=floor(sqrt(n)/(8000d)), and gives the same
exponential conclusion. There is no row-count hypothesis at all. Arbitrarily
many braid rows, output-only rows, rows removed by normalization, and rows
with support larger than n are permitted. Arbitrarily many other rows are
permitted whenever their stated weighted sum satisfies the budget.

This weighted theorem still counts multiplicities. The separate
`feeding/ProfileConditional.lean` branch removes multiplicity by using
distinct support sets, allowing nonproportional rows with the same support.
It does not identify or merge the actual neurons. Its raw support-profile
and arbitrary preliminary-restriction extensions have their own checks.

## Mechanism and verification scope

The absorption construction masks output-only rows in the first dictionary
and places their contributions in auxiliary second slots with linear
preactivations. Their actual interaction graphs are empty. A positive-size
matching event is impossible for those slots, so the probability sum still
counts only the original h₂, rather than the enlarged auxiliary width.

A paired half restriction contains a fixed support of size r with probability
at most 2^-r. Actual generic localization either preserves the whole support
on the selected coordinates or makes that row linear/zero. It never creates
a partial-support nonlinear row. Exact first-row lineage removes rows with
nonzero original bias or nonzero coordinate sum. Supports larger than the
selected arity cannot survive and can be omitted outright.

The independent drivers `WidthTradeoffCheck.lean`, `SharpTradeoffCheck.lean`,
and `WeightedTradeoffCheck.lean` expand all nine raw arrays, the actual
evaluator, original W-column count, support filters, matching order, and
constants. Integer rounding controls include zero width, odd ambient arity,
and a jump at a perfect square. The separate absorption and weighted-model
gates include actual network controls. No joint large-arity H/network
nonvacuity witness is claimed: growing H remains an open structural premise.

Run the content-bound research gate with

    python3 research/sN/overnight_20261103/h1_tradeoffs/recheck.py --run

These are isolated research declarations until separately integrated or
published. A receipt records exact source hashes, actual type checks, and
standard-axiom audits; it does not establish H.
