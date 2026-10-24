# Five-input fixed-layer second-width improvement

**Status: exact finite certificate and a mathematical locality reduction;
independently checked, not Lean verified.**

Let `V=span{x_i, sigma(x_i-x_j): i<j}` on five coordinates. Define `k(5)`
as the least number of free outer neurons in an identity

```
max_5 = R + sum_(j<K) d_j sigma(g_j),   R,g_j in V.
```

The new result is

```
3 <= k(5) <= 4.
```

The upper identity with four free neurons was already certified. The new
lower bound excludes every two-neuron representation, with arbitrary
real coefficients, using the exact certificate below.

Consequences in the no-skip architecture, counting every neuron:

* For the paper's fixed 16-feature first layer, `5 <= h2* <= 6`.
* For the fixed 10-feature first layer of `netB_10_6.json`, the subsequent
  complete K=3 certificate now proves `h2*=6`; see
  `overnight_fixed_bowtie.md` for the matching result and proof gate.

The full paper layer remains undecided between five and six. These
statements do not say that every unrestricted first layer requires
second width five.

## Why the fixed-layer width gains two

For the paper layer, the existing Theorem A in `PROOFS.md` proves
`h2*=k(5)+2`, by comparing translations towards positive and negative
infinity. It applies after relabeling to any reference coordinate.

The 10-feature construction uses eight coordinate-difference ReLUs and
`sigma(x1),sigma(-x1)`. Every one of its features belongs to the linear
span of the paper's first layer based at coordinate1. Thus any network
with that fixed 10-row layer can be implemented with the full paper
layer at the same second width. The lower bound five transfers. The
existing `(10,6)` exact network supplies the upper bound six. The
subsequent stronger fixed-layer equations in `overnight_fixed_bowtie.md`
close this gap exactly.

More generally, the lower bound five applies when every zero-sum
first-layer row is a coordinate difference and there is exactly one
positive-sum and one negative-sum first-layer row. The two carrier
hyperplanes need not coincide. At each translation end, K2 exclusion
forces at least three zero-slope neurons. If the second width were four,
the positive and negative ends would have distinct unique passing
neurons, leaving two common free neurons. Comparing the two identities
gives a globally nonnegative linear function equal to a positive sum of
two negative-part functions. The linear function must vanish, so both
passing neurons can be absorbed into the unrestricted linear-plus-pair
remainder. This contradicts the K2 certificate.

## Exact necessary equations

Translation to infinity allows every free preactivation to be taken
translation invariant, without increasing the free-neuron count.
Positive homogeneity absorbs each nonzero output magnitude into its
preactivation, leaving output signs `d_j in {+1,-1}`.

Write `v(S)=g(1_S)`. This is a quadratic Boolean set function with
`v(empty)=v([5])=0`. At a top triple tie `T` with the other labels in
the strict order `(o,p)`, a neuron can contribute only when
`v(T)=v(T union {o})=0`. At a four-label tie `U`, it can contribute only
when `v(U)=0`. The full five-label tie always has `g(0)=0`.

For a contributing neuron and a tie set `U` of size at least three,

```
2 mu_U(sigma(v)) = sum_(empty != S proper subset U)
                      (-1)^(|U|-|S|) |v(S)|.
```

Indeed `sigma(t)=(t+|t|)/2`, the mixed difference of the degree-two
function `v` vanishes, and `v(U)=v(empty)=0`. The target mixed
difference is `(-1)^(|U|+1)`. This gives 20 triple equations, five
four-tie equations, and one five-tie equation. The pair-feature
remainder is annihilated in every case. These are necessary equations,
so their inconsistency suffices for exclusion; their consistency
would not certify a global network identity.

## Exhaustive continuous-parameter coverage

The 15 values on triples and four-sets have exactly one relation:

```
sum_(|S|=3) v(S) = 3 sum_(|S|=4) v(S).
```

In independent quadratic Boolean coordinates, their matrix has exact
rank14, and every coefficient of this relation is nonzero. Thus every
14 of the forms are independent. Every nonzero vanishing flat is
specified by a zero set of size at most13, giving32752 flats. The
zero preactivation contributes nothing and can be discarded.
If only one nonzero preactivation remains, it must vanish on all20
triple localities. This forces all15 relevant values to vanish, and
rank14 then forces that preactivation to be zero as well. Thus no
zero-neuron boundary case is omitted by enumerating nonzero pairs.

For each first flat, the triple localities it fails to cover force a
specific set of zeros in the second flat. Enumerating all supersets of
those forced zeros gives97961 unordered covering pairs, or1193 pairs
up to coordinate permutation and neuron exchange. The independent
coverage program regenerates these pairs without importing the old
flat-enumeration or orbit-generation implementation.

For every pair, all four output-sign choices are checked. On each
flat, equal or proportional absolute-value forms are combined
exactly. Independent reversal of each preactivation preserves its
absolute-value equations, so one form per neuron may be fixed
nonnegative. Every further branch includes both closed signs. This
covers all real coefficients and all boundary and irrational cases.

## Certificate and independent checker

The search produced4772 exclusion trees. It used63997 LP proposals,
but the final proof does not trust their statuses. The durable trees
contain33385 binary splits,7545 direct constant contradictions, and
30612 rational Farkas contradictions. The complete compressed proof
is approximately84KiB.

`overnight_fixed_k2_verify.py` uses only Python's standard library.
It does not import the search, its equation reduction, or an LP solver.
For every case it:

1. Checks the declared flat bases against the original ray equations,
   their exact dimensions, and their independence.
2. Regenerates all unreduced signed cube equations directly.
3. Verifies rational row-space equality with the proposed compressed
   equations; no equation-compression correctness is assumed.
4. Checks the independent global sign symmetries and every binary
   closed-sign branch.
5. Verifies every constant contradiction and every Farkas identity by
   rational addition and multiplication, including nonnegativity of
   all inequality multipliers.
6. Checks complete coverage of1193 pairs times four output signs.

The independent check passed in40.3 seconds. The finite theorem still
uses the written mixed-difference/translation bridge above; it is not
a kernel-level Lean theorem.

## Reproduction

From this directory, using the existing research environment:

```
P=../dfs/h4-general-neurons/venv/bin/python
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 "$P" overnight_fixed_coverage.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 "$P" overnight_fixed_k2_certify.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 "$P" overnight_fixed_k2_systems.py
python3 overnight_fixed_k2_verify.py
```

The producer has a1200-second wall-time budget. It completed in66.9
seconds; its hash and artifact hash are in
`overnight_fixed_k2_producer.json`. Exact checker receipts and source
hashes are in `overnight_fixed_k2_check.json` and
`overnight_fixed_coverage.json`. The old `k2b_done.txt` verdicts are not
needed: all4772 cases have been recomputed and certified afresh.

## Fixed bowtie layer and next search

Set `u=x0-x1`, `v=x2-x1`, `s=x3-x1`, `t=x4-x1`. The certified 10-row
layer consists of

```
sigma(u), sigma(u-v), sigma(-v), sigma(v),
sigma(s), sigma(-t), sigma(t), sigma(s-t), sigma(x1), sigma(-x1).
```

Its eight translation-invariant features give 310 locality-coverage
masks, including zero. Complete enumeration gives 30,041 covering
triples of nonzero vanishing flats. All eight output-sign choices have
now been independently excluded, including the six zero-coverage flats;
see `overnight_fixed_bowtie.md`. The earlier counts 309 and 30,029 omitted
those six flats and are superseded.

The natural eight-row candidate keeps the four positive differences
`sigma(u),sigma(v),sigma(s),sigma(t)`, the two comparisons
`sigma(u-v),sigma(s-t)`, and the carriers `sigma(+-x1)`. Its features
determine the target value, since `max_5-x1` is the maximum of the
four positive differences. Whether a single additional hidden layer
can represent that maximum using precisely these features remains
open. Removing the reverse features cannot silently preserve the
linear carries in the known six-neuron second layer.
