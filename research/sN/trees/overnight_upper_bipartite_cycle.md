# A symmetric graph family of exponential size: exact first obstruction

25 October 2026. This is a closed construction branch, not a lower bound for
all cyclic or weighted graph units. It stays outside the paper: there is no
matching construction.

The candidate uses two interchangeable vertex classes A,B, a distinguished
head root r and reference a. Its preactivation is

    x_r-x_a
      + c_AB sum_(i in A,j in B) sigma(x_i-x_j)
      + c_A sum_({i,j} subset A) |x_i-x_j|
      + c_B sum_({i,j} subset B) |x_i-x_j|,

with c_AB,c_A,c_B in {-1,0,1}. We include both variants: A,B partition the
labels other than a, or partition all labels (allowing comparisons incident
to a). Apply one outer ReLU. Within-class absolute values are implemented
by the two opposite comparison ReLUs. These are actual two-hidden-layer
units, including dense comparison graphs with arbitrarily many cycles.

All label assignments of these finitely many parameter types give
O(N^2 2^N) descriptions. Adjoining every canonical oriented star with every
root adds only O(N^3 2^N). We also allow an arbitrary linear function and a
linear combination of the comparison ReLUs sigma(x_i-x_j). Thus this was a
concrete exponential-size dictionary candidate broader than trees.

It does not span max_5. A full symmetric orbit calculation gives the exact
rank gates

| Family | Distinct columns | Rank / augmented rank |
|---|---:|---:|
| Reference label excluded from comparisons | 74 | 69 / 70 |
| Same, plus all canonical oriented stars | 77 | 72 / 73 |
| Both graph variants, plus all stars | 220 | 125 / 126 |

These columns include the symmetric shallow comparison remainder. The
first calculation consolidates every interior hyperplane on an ordered
braid cone and checks the remaining linear gradient with exact rational
arithmetic. It is implemented in `overnight_upper_bipartite_cycle.py`.

## An independent integer-value certificate

The exclusion does not rely on the wall calculation or its rank code.
`overnight_upper_bipartite_values_certificate.json` contains 119 integer
input points and integer weights. The standard-library command

    python3 research/sN/trees/overnight_upper_bipartite_values.py check

directly evaluates all 556 raw orbit representatives, with all 120 input
permutations in each orbit. The weighted evaluation sum is zero for every
such function and for the symmetric sum of absolute pair differences.
It is nonzero for 5 max_5(x)-sum_i x_i. The checker imports no wall producer,
matrix library, optimizer, or numerical rank routine. The fresh check
passed in about 40 seconds.

This excludes nonsymmetric expansions too. The dictionary is closed under
all coordinate permutations; averaging any proposed identity gives an
identity in these orbit sums. A symmetrized shallow comparison remainder
is a multiple of the absolute-pair sum plus a linear multiple of the
coordinate sum. The latter coefficient is forced by diagonal translation,
and is removed in 5 max_5-sum_i x_i.

Scope matters: this gate fixes the three inner coefficients to {-1,0,1}
and the head to x_r-x_a. Arbitrary real heads, other coefficient ratios,
three or more vertex classes, and arbitrary shallow linear forms are not
excluded. The result does not reject exponential constructions using
cycles in general.
