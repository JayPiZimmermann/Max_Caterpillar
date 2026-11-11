# Independent audit of the first-width tradeoffs

The review found no mathematical or model-scope gap in the width-parameter
and feeding-only extensions. `WidthTradeoffCheck.lean` is an independently
written exact-contract driver; its current verification result is recorded
by the enclosing recheck receipt, rather than inferred from this prose.

## Actual model and indices

The contracts expand all nine arrays of the original affine-skip network:
first covectors and biases, second-layer weights and direct input heads,
second biases and output coefficients, first-to-output coefficients, and
the final affine term. They assert equality with the actual maximum on
every real input. The conclusion uses the original second width.

There is no assumption that the original first covectors are braid
differences, homogeneous, bounded in support, rational, or generic. Recession,
translation normalization, generic localization, and simultaneous support
budgets are proved dependencies. The raw wrappers retain both original
finite hidden-layer index types.

The feeding contract literally counts

    card { j : Fin h1 | there exists k : Fin h2 with W[k,j] != 0 }.

This is a count of columns of the original second-layer weight matrix.
It is not a count after pruning, and it is not inferred from the output
coefficients or from nonzero first-row covectors. Counting a redundant or
zero-covector column can only weaken the resulting bound.

## Why output-only first neurons cost no second width

The masked `core` first layer retains every feeding covector and replaces
other covectors by zero. This leaves all original second preactivations
unchanged. The exact `absorb` model reintroduces every first-to-output term
as an auxiliary outer ReLU with a linear preactivation and zero incoming
first-layer weights. Its evaluator equals the original evaluator.

Every auxiliary interaction graph is empty. Because the Bernoulli
parameters prove that the matching order is positive, the auxiliary
matching event is empty for every selected set, tail order, and scale.
The conditional mean is zero, and summing the union bound leaves exactly
the original second indices. This is a proof about the actual events; it
does not assume that arbitrary output-only covectors are themselves braid
covectors.

Normalization cannot create a new feeding column: its feeding count is
bounded by the literal original count above. The raw half-restriction
budget is consequently charged only to original feeding columns.

## Sharper simultaneous half budget

The stronger extension uses one selected half and the pointwise cost

    J(r) = max(105, 2 (r)_4) for r>=3, and zero otherwise.

The proved inequality 8 J(r) <= 105 2^r allows the same paired averaging
argument to produce a single model with 16L <= 105F and 8M <= F, where F
is the original feeding count, L is the actual fourth falling support
moment, and M is the non-braid row count. This avoids choosing different
halves for the two budgets. Restriction cannot create a new feeding row,
so the original F remains valid.

Consequently 105F <= 16 d^2 n^2 discharges both Bernoulli budgets. The
resulting sharp parameter is sqrt(105F/(16n^2)) rounded by the same integer
rule below. `SharpTradeoffCheck.lean` separately expands the literal
original W-column count, the 105/16 budget, and the improved quadratic
coefficient denominator 48000 ceil(sqrt(C)). No total-width hypothesis is
inserted by this stronger contract.

## Parameter rounding and scope

Write n = floor(N/2) and h for either the total first width or the original
feeding count. The explicit integer parameter is

    d = floor(sqrt(floor(81 h / (4 n^2)))) + 1.

For n > 0, the strict square-root bound and the integer division inequality
give 81h <= 4 d^2 n^2. The added one is essential at a perfect-square
quotient. The driver checks the zero-width value, even and odd ambient
arities, and both sides of a square-quotient jump. The size condition with
d >= 1 derives positivity of both N and n, so there is no unproved
nonzero-dimension premise.

The stronger feeding parameter replaces 81h/(4n^2) by 105F/(16n^2).
Its separate rounding contract proves 105F <= 16 d^2 n^2 for every n>0.

The conditional conclusion is

    h2 >= (1/2) exp(3 sqrt(n) / (8000 d)),

under the explicit structural obstruction H(4q+1,q), where
q = floor(sqrt(n)/(8000d)). The driver expands this q rather than accepting
an unspecified matching-order parameter.

The quadratic cap has been removed, but the size condition still restricts
h to a small-constant cubic regime. The theorem must not be described as
an exponential lower bound for arbitrary first widths. In scaling terms,
for positive h the exponent is of order min(sqrt(N), N^(3/2)/sqrt(h)); it grows faster than
log N if h = o(N^3/log^2 N). At h proportional to N^3 it is only constant.

For h1 <= C N^2, the separate integer ceiling parameter gives a loss of
order sqrt(C), improving the earlier linear loss in C. The definition
`sqrtCeiling C = sqrt(C-1)+1` has the harmless value one at C=0; its intended
ceiling interpretation is exact for C>=1.

## Weighted original-support extension

The separately checked support-sensitive extension replaces the feeding
count by a weighted sum on the original arrays. A row of support size r is
charged only when its original bias is zero, its coordinate sum is zero,
and its original W column is nonzero. Supports larger than n cost zero.
The remaining charge is w(r)/2^r, with w(3)=1, w(r)=(r)_4 for r>=4, and
w(r)=0 for r<=2. `WeightedTradeoffCheck.lean` expands every one of these
gates and defines r by the literal filter of nonzero coordinates of A.

The weighted averaging proof needs only nonnegative costs and cost(0)=0.
It uses the exact upper bound 2^(-r) for a support to survive a paired half
selection. If a support contains both members of a pair, its survival
probability is zero, so independence of all original supports is not being
assumed. Actual localization preserves an entire original support or
zeros the row; it does not truncate a support and then assume monotonicity
of the cost. The generic model bridge proves both statements. Raw bias,
coordinate-sum, and feeding masks are justified by the original-array
normalization identities. Clipping is valid because an n-dimensional
surviving row cannot have support larger than n.

Both Bernoulli budgets are bounded by the same weighted cost on the same
actual selected model. This permits arbitrarily many first rows whose
weighted contribution is zero or sufficiently small. It does not permit
arbitrarily many bounded-support eligible rows at no cost.

## Unresolved premise and evidence boundary

The growing-order structural obstruction H remains a genuine hypothesis.
Neither these wrappers nor the empty-auxiliary-event argument proves it.
No concrete joint witness for the large-size network/H hypotheses is
claimed. Small parameter controls check arithmetic, and the feeding
development has a separate output-only support control; those are not
substitutes for H.

This audit concerns isolated research declarations. Public integration,
fresh closure rebuilds, exact-type checks and allowed-axiom checks are
recorded separately by the parent verification gate.
