# Raw affine-skip general-row bound with quadratic total first width

New public leaf: `GrowingMatching/AffineGeneralRows.lean`.

The headline
`GrowingMatching.AffineGeneralRows.conditional_affine_quadratic_width_lower_bound`
takes an original nine-array affine-skip network with arbitrary real
parameters, biases, input/output skips and first covectors. Its identity is
required on all real inputs. The width budget counts every original first
neuron, including output-only terms: `h1 <= C*N^2`, with integer `C>=1`.

Put `n=floor(N/2)` and `d=20*C`. For `q>=1`,

    8000*d^2 <= n,       1000*d^2*q^3 <= n,

and the explicit local obstruction `H(4*q+1,q)`, the theorem gives

    h2 >= (1/2)*(n/(400000*d*q^2))^q.

The right side involves the original second hidden width. No normalization,
model, support-size, overlap, moment, probability, or rank hypothesis is
provided by the caller. Dimension positivity is proved internally. The
obstruction remains open at growing q: this is a conditional finite
superpolynomial route, not an unconditional lower bound of that order.

The new `Half.lean` helper applies the existing faithful affine-skip
normalization, then selects an actual half coordinate set via the existing
weighted restriction theorem. Only wholly contained supports survive; odd
ambient dimensions are handled without identifying inputs. Generic tied
localization preserves both original hidden-layer index sets. It yields
simultaneously `4*A<=81*h1` and `4*M<=h1` for the fourth moment A and
non-braid count M of ALL indexed first rows. Output-only rows are included.

The new `Budgets.lean` uses `N<=3*n`, valid for positive `n=floor(N/2)`.
Thus `4*A<=729*C*n^2`; `729*C<=4*(20*C)^2` gives `A<=d^2*n^2`.
The support-at-least-three count and sum of falling fourth support powers
are each bounded by A. These are exactly the two literal statistics
required by `GrowingMatching.conditional_general_rows`.

The independent driver expands the original nine-array evaluator, all
normalization sums, the ALL-first half statistics, the literal integer
parameter `20*C`, the original total first-width budget, the floor arity,
and the final inequality. It checks actual odd-arity MAX3-to-MAX1
restriction and an independent oddN7 scalar contract. It asserts no
growing-order obstruction.

Reproduce:

    python3 research/sN/jensen_bound/affine_general_rows_recheck.py --run
