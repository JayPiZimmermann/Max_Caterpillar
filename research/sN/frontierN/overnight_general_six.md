# Every first-width-eight max-five network has the bowtie first layer

**Status (2026-10-25): complete finite real-coefficient classification, independently checked, with the mathematical bridge below. Not Lean verified. Research only: no construction attaining the resulting lower bounds is known.**

If a two-hidden-layer ReLU network without skip connections computes `max_5` exactly on `R^5` and has first hidden layer width eight, then, after removing biases, permuting inputs/neurons, and positively rescaling individual first-layer rows, its first-layer functions are exactly

```
sigma(x0), sigma(-x0),
sigma(x1-x0), sigma(x2-x0), sigma(x3-x0), sigma(x4-x0),
sigma(x1-x2), sigma(x3-x4).                                  (B)
```

Either matching edge may initially have the opposite orientation; swapping its endpoints puts it in the displayed form. This classifies necessary first layers; it does not assert that any second layer over (B) computes the maximum.

Combined with the certified four-free-neuron exclusion in
[`overnight_fixed_natural8.md`](../best5/overnight_fixed_natural8.md), this gives

```
h1 = 8  =>  h2 >= 7.
```

Together with the separately established `h1>=8` and the uniform Lean-verified `h2>=ceil(N/2)+1`, every unrestricted five-input network therefore has total hidden width at least thirteen. The pairs `(8,4)`, `(8,5)`, and `(8,6)` are excluded, but `(9,4)` is not excluded by these results. The known `(10,6)` construction shows that the minimum second width can depend on the first width; the attained unrestricted tradeoff and Pareto frontier remain open.

## Reduction to six zero-sum rows

The five-row certificate in `overnight_general.md` shows that a singleton positive-sum or negative-sum first-row class requires at least six zero-sum rows. The existing C3/C4 support lower bound requires at least five zero-sum rows. Thus at total first width eight the row-sum classes must have sizes `(1,1,6)`.

Every zero-sum row is nonzero: otherwise the factorization below would use at most five nonzero features, already excluded. Its exact support therefore has size two, three, four, or five. Repeated supports are allowed.

For either signed singleton class, diagonal translation yields a global factorization

```
max_5(x) = ell(x) + Phi(sigma(r_1 dot x),...,sigma(r_6 dot x)), (1)
```

with fixed linear `ell` and zero-sum rows `r_j`. No regularity assumption on `Phi` is required for the necessary conditions used here.

At a strict feature cell with active row set `A` and unique maximum label `a`, the feature-fiber argument gives

```
e_a - ell belongs to span{r_j : j in A}.                     (2)
```

Indeed, every vector annihilating the active rows locally preserves every ReLU feature, so (1) forces its `ell` slope to equal its `a`-coordinate slope. The annihilator of the common kernel is the row span. The analytic slope argument itself is Lean checked as `feature_fiber_slope` in `overnight_general_bridge.lean`.

## Finite flags cover all real coefficient magnitudes

The supports satisfy the existing C3 and C4 conditions from `best5/PROOFS.md`. The independent checker enumerates every multiset of six subsets of sizes two through five. Exactly 2767 labelled multisets satisfy C3/C4; they comprise 43 coordinate-permutation orbits.

For every row, all nonzero coefficient-sign patterns containing both signs are enumerated. There are 58176 profiles across the 43 support representatives. Every real zero-sum row with the stated exact support belongs to one profile, including arbitrary irrational and arbitrarily small nonzero coefficients.

For any priority ordering and coordinate signs `eps_i`, take `x_i=eps_i B^(priority(i))` with `B` sufficiently large. Each row has the sign of its highest-priority nonzero coefficient times the corresponding `eps_i`. The maximum coordinate is also determined by the priority/sign data. This is the same leading-coefficient argument as the five-row certificate. A common sufficiently large `B` exists for all finitely many rows and flags at any fixed real coefficient choice. The functional `ell` in (1) is the same for every flag.

## Three necessary conditions, with elementary cut witnesses

The initial component equations say that if each active row is wholly inside or outside a coordinate subset `C`, then

```
ell(C) = 1_{a in C}.                                        (3)
```

All negative lexicographic flags exclude 55839 profiles. Adding every signed lexicographic flag excludes another 1300. The remaining 1037 profiles are checked using explicit cut-removal witnesses.

**Two-winner test.** If two flags have the same active row set `A` but different maximum labels `a,b`, subtract their instances of (2):

```
e_a-e_b belongs to span{r_j : j in A}.                       (4)
```

Suppose a cut `C` does not separate `a,b`, and exactly one remaining row crosses `C`. All wholly contained or disjoint rows have coefficient sum zero on `C`. If the crossing row's sum on `C` is nonzero, its coefficient in any representation (4) must vanish. Nonzeroness follows purely from the recorded signs whenever all its coefficients on either side of the cut have one strict sign. Delete that row and repeat. If the remaining rows cannot cross a cut separating `a,b`, equation (4) is impossible. The independent checker verifies each deletion and the final separating cut. This excludes another 1031 profiles.

**Global-ell test.** For two residual profiles, use (2) directly. Whenever the already established equations (3) force `ell(C)=1_{a in C}`, the target `e_a-ell` has sum zero on `C`, so the same unique-crossing-row deletion is valid. The reduced row set gives further equations (3). The recorded traces reach inconsistent equations in both cases. Each forced equation and each cut deletion is independently checked.

Exactly four profiles remain. All have supports

```
{01,02,03,04,12,34},
```

the first four rows have sign `(-,+)`, and the two matching rows may have either orientation. Since a zero-sum row on a pair is a positive multiple of its oriented coordinate difference, these are precisely the zero-sum features in (B). The checker also verifies that their component equations uniquely force `ell=e_0`.

## Why the two signed carriers are coordinate carriers

Let `p` be the unique positive-sum first row and `s_p=a_p dot 1>0`. In the positive translation reduction, zero-slope second neurons have coefficient zero on this row. The linear part in (1) is therefore `c*a_p`, where the diagonal slope identity gives `c*s_p=1`. Hence `ell=a_p/s_p`.

The finite classification forces `ell=e_0`, so `a_p=s_p e_0`. The negative-end argument gives the same identity for the unique negative-sum row `q`: `a_q/(a_q dot 1)=e_0`, with negative denominator. Thus the two signed carriers are positive multiples of `sigma(x0)` and `sigma(-x0)`. No antipodality assumption was imposed; it is a conclusion.

## Consequence for the second width

Let `W6` be the span of the six zero-sum features in (B), and let `k_W6`
be the least number of outer ReLUs in a representation

```
max_5-x0 = R + sum_j d_j sigma(g_j),    R,g_j in W6.
```

The two-translation argument in
[`overnight_fixed_bowtie.md`](../best5/overnight_fixed_bowtie.md#reduction-to-four-free-neurons)
applies to any invariant span together with the two carriers
`sigma(x0),sigma(-x0)`. It gives the exact relation `h2*=k_W6+2` for (B).
In particular, a hypothetical network of width `k_W6+1` would have one
passing neuron at each translation end. Their output signs are opposite;
subtracting the two translation identities forces their negative parts
to vanish. Both passing terms then belong to the remainder, leaving
only `k_W6-1` free terms, a contradiction. No assumption that `W6`
contains every linear function is needed.

The natural-eight certificate excludes all four-free-neuron
representations over `W6`: 3,418 covering flat quadruples and all sixteen
output-sign choices, for 54,688 cases. Every case has a direct rational
Farkas separation using fifty necessary locality and ray equations.
The independent coverage checker enumerates all real-parameter strata;
the equation checker verifies each rational contradiction without a
numerical solver. Repeated flats allow padding any representation with
one to three terms to four; the fifth mixed difference excludes zero
terms. Thus `k_W6>=5`, hence `h2>=7`.

The independent checks are `overnight_fixed_natural8_coverage.py` and
`overnight_fixed_natural8_verify.py`, with receipts
`overnight_fixed_natural8_coverage.json` and
`overnight_fixed_natural8_check.json`, all in `research/sN/best5/`.
Together with the classification above, this covers arbitrary real
weights and all biases in an unrestricted first-width-eight network.
It does not prove that any finite second width over (B) is sufficient.

## Independent checker and arithmetic trust boundary

Run:

```
python3 research/sN/frontierN/overnight_general_six_check.py
```

It completed in 11.24 seconds and exited zero. It imports no producer. It independently enumerates support and sign coverage, uses the opposite priority convention from the producer, constructs active components by graph reachability, and validates each recorded cut witness. Its only three input artifacts are `overnight_general_six_supports.json`, `overnight_general_six_pairpeeling.json`, and `overnight_general_six_global.json`; their hashes are recorded in the receipt.

The linear systems in `ell` have at most six columns including the right side, and all entries are zero or one. Every square minor has absolute determinant at most `6!=720`. Arithmetic modulo the prime 1009 therefore preserves **every** rank exactly over the rationals, including augmented matrices and tests that a cut equation is implied. Rational and real consistency coincide for these rational systems. This is a bounded-determinant proof of exactness; it does not use the invalid inference from a generic modular rank gap to a real exclusion. No modular arithmetic is applied to the unknown real row coefficients.

To reproduce all necessary producer artifacts:

```
python3 research/sN/frontierN/overnight_general_six.py supports
python3 research/sN/frontierN/overnight_general_six.py signs
python3 research/sN/frontierN/overnight_general_six.py full
python3 research/sN/frontierN/overnight_general_six_pairpeeling.py
python3 research/sN/frontierN/overnight_general_six_global.py
python3 research/sN/frontierN/overnight_general_six_check.py
```

All completed phases used one thread, stayed below the 120-second branch budget, and used small memory. Canonical-coefficient and symbolic-Groebner probes helped discover the cut criterion but are not dependencies of the checker or proof. The classification remains an exact checked finite argument with a written model bridge, not a Lean-verified network theorem.
