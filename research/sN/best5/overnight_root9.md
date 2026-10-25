# A six-neuron lower bound for the certified nine-row first hidden layer

25 October 2026. This result stays in the research notes: the best currently
certified construction on this first hidden layer has second width 14, so the
bounds do not match.

Fix exactly the first hidden layer in `overnight_fixed_cross_net9_17.json`.
With `u=x_1-x_0`, `v=x_2-x_0`, `s=x_3-x_0`, `t=x_4-x_0`, its seven comparison
functions are

`sigma(u), sigma(v), sigma(v-u), sigma(s), sigma(t), sigma(s-t), sigma(v-t)`.

The last two features are `sigma(x_0),sigma(-x_0)`. For this fixed layer,
arbitrary real second-layer and output weights require **h2>=6** to represent
the maximum of five inputs. Arbitrary biases do not improve the bound, by
recession. Together with the independently verified construction, the current
fixed-layer interval is **6<=h2_min<=14**; the upper network is in
`overnight_fixed_cross_net9_14_simple.json`. No statement about all first hidden
layers of width nine follows from this certificate.

## Model reduction

Let `W` be the span of the seven comparison functions and `f=max_5-x_0`.
Define `k_W` as the least number of terms in

`f=R+sum_(j=1)^k d_j sigma(g_j), with R,g_j in W`.

The translation-carrier proof in `overnight_fixed_bowtie.md` applies unchanged:
the optimal second width is `k_W+2`. Its proof does not assume that `W`
contains all linear functions. For completeness, at both translation ends
at least `k_W` neurons have zero carrier slope, and at least one neuron
passes the required linear growth. If width were `k_W+1`, the unique passing
neurons at the two ends would be distinct with opposite output signs.
Subtracting the two translation identities forces both of their negative
parts to vanish. Absorbing those terms into `W` leaves only `k_W-1` nonlinear
terms, a contradiction. The upper compilation uses two opposite ReLUs for
the linear carrier and remainder.

It therefore suffices to exclude `k_W<=3`.

## Complete real domain and exact contradictions

The fifteen vanishing forms `g -> g(1_U)` for `|U|=3,4` give ten distinct
hyperplanes in the seven-dimensional space `W`. Their intersections have 383
flats, including zero. Every real preactivation has one of the 382 nonzero
vanishing profiles or is zero.

For a top triple `U` with next label `o`, only a preactivation vanishing on
both `1_U` and `1_(U union {o})` contributes to the third mixed difference.
For a top four-label tie it must vanish on `1_U`. Grouping proportional
absolute-value forms checks whether the relevant mixed difference is
identically zero on a flat. These conditions give 25 required locality bits.

No pair of flats covers all 25 bits. There are 217 unordered covering triples,
all with three distinct flats. With the eight output-sign assignments, this
leaves 1736 cases. Nonzero output magnitudes are absorbed into their
preactivations, without bounding any real coefficient. Repetition and
zero terms are covered: a representation using fewer terms can be padded
by splitting a nonzero term into positive copies; with no nonlinear terms,
the fifth mixed difference is impossible.

In every case the checker reconstructs 26 locality equations and 23 Boolean-ray
equations. The latter are the left kernel of the rank-seven feature matrix
on all 30 nontrivial Boolean rays and eliminate the arbitrary remainder `R`.
Each of the 1736 cases has a rational Farkas contradiction using only those
direct equations and nonnegativity of absolute values. No sign-tree search,
strict sign assumption, bounded coefficient box, or numerical infeasibility
verdict is needed in verification.

The independent checker enumerates all subsets of the ten hyperplanes,
rather than the producer's successive-intersection traversal. It checks
every flat row space and every locality mask. A separate count by pairs of
coverage masks proves completeness of the 217 triples; all eight sign cases
and every rational contradiction are then checked. The complete replay
passed in 1.44 seconds using only the Python standard library.

```
python3 research/sN/best5/overnight_root9_verify.py
```

The receipt is `overnight_root9_check.json`. The shared direct arithmetic
checker is `overnight_fixed_bowtie_verify.py`; it imports no search code or
LP solver. This is an exact finite certificate with the mathematical
generic-tie and translation bridges above, not a Lean theorem.

## Construction target

A globally verified `(9,6)` network on these features would match this lower
bound. Its existence remains open. The four-neuron necessary domain already
has 296,861 unordered covering quadruples, so it is not the small 1736-case
exclusion just proved. Neither failed sparse searches nor a feasible
absolute-value relaxation decides that construction question.
