# Five-input unrestricted first-width improvement

**Status (2026-10-24): exact finite certificate, independently checked, with the mathematical model bridge below. Not Lean verified.**

For an exact two-hidden-layer ReLU network computing `max_5` on all of `R^5`, with arbitrary real weights and biases, no skip connections, and every neuron counted:

* `h1 >= 8`.
* If `h1 = 8`, then `h2 >= 4`; equivalently, `h2 = 3` implies `h1 >= 9`.
* Consequently `h1 + h2 >= 12`.

The subsequent independent argument in `overnight_general_second_width.md` excludes second width three for every first width, so the combined lower bounds are `h1>=8`, `h2>=4`. The existing certified upper construction is `(10,6)`; the Pareto frontier and improved constructions remain open. The first-width certificate itself only gives the conditional second-width consequence stated above.

The exact intermediate statement is stronger and useful independently:

> If exactly one first-hidden-layer row has positive coordinate sum, or exactly one has negative coordinate sum, then at least six rows have coordinate sum zero.

The proof uses the existing support conditions C3 and C4 and a finite necessary condition for the five-row ReLU feature map. It covers continuous real coefficients by their signs, not by a bounded coefficient grid. The general conjecture that the cell condition forces a full star is unnecessary.

## Model and reductions already established in the repository

Write `sigma(t)=max(0,t)`. After bias removal the network has the form

```
F(x) = sum_k d_k sigma(sum_j W_kj sigma(a_j dot x)).
```

Bias removal preserves widths and the function: divide `F(t*x)` by `t>0` and let `t` tend to infinity; every bias tends to zero, while `max_5(t*x)/t=max_5(x)`. Output bias, if included in the convention, also disappears. This is the existing `Network.eval_zeroBias_of_posHom` theorem in `MaxCaterpillar/Frontier/Basic.lean`.

Let `J+`, `J-`, and `J0` be the first-hidden-layer indices whose coordinate sums are positive, negative, and zero. Both `J+` and `J-` are nonempty because `F(t*1)=t` for both signs of `t`.

The existing local restrictions (best5/PROOFS.md, Theorem H1) say that the nonzero supports of rows in `J0` satisfy:

* C3: every three-element subset contains one of these supports.
* C4: for every four-element set `I` and every `a in I`, some support `S` satisfies `a in S subset I`.

A zero-sum nonzero row has support size at least two. Supports of size five, zero rows, and repeated supports do not help these conditions. Exact finite enumeration shows that at least five distinct useful supports are needed. With precisely five, up to permutation of coordinates the families are

```
F1 = {01, 02, 13, 24, 34},
F2 = {01, 02, 034, 13, 24},
F3 = {01, 02, 123, 124, 34}.
```

The new independent checker re-enumerates every subset family of size at most five from the 25 subsets of sizes two through four. There are no covers below five and exactly 102 labelled covers at five; all 102 belong to these three permutation orbits. Thus no support-size boundary, zero row, repeated support, or coefficient degeneracy is omitted.

## The singleton-row reduction

Suppose `J+={p}`. Translate the input by `t*1` and let `t` tend to positive infinity. The established asymptotic identity splits second-hidden-layer neurons into positive, negative, and zero asymptotic slopes. A zero-slope neuron has `W_kp*(a_p dot 1)=0`, hence `W_kp=0`. Therefore for a linear functional `ell` and a function `Phi` of the `J0` features,

```
max_5(x) = ell(x) + Phi(sigma(r_1 dot x), ..., sigma(r_m dot x)),    (1)
```

where the `r_j` are the zero-sum rows. Negative-slope second-layer terms disappear; positive-slope terms give the linear part plus linear combinations of the features; zero-slope terms give ReLUs of linear combinations of the features. There is no restriction here on the number of second-hidden-layer neurons. Translating to negative infinity gives precisely the same reduction when `|J-|=1`.

Suppose now `m=5`. The support enumeration reduces to `F1,F2,F3`. We show that none can satisfy (1), for any nonzero real coefficients on its stated supports.

## A coefficient-independent consequence of (1)

Fix an ordering `p_0,...,p_4` of the coordinates. Give coordinate `p_k` priority `k` and put

```
x_i = -B^(priority(i)).
```

For any fixed real rows, choose `B>=2` sufficiently large. The sign of `r_j dot x` is exactly the sign of

```
-r_j(i),   i = the highest-priority coordinate in support(r_j).       (2)
```

This follows from the leading coefficient of a nonzero polynomial. Explicitly, it suffices to take `B` larger than the ratio of the sum of the absolute coefficients of each row to its smallest nonzero absolute coefficient. There are finitely many rows, and all nonzero coefficients may be arbitrary reals. Hence all strict row signs in (2) hold simultaneously; no irrational or arbitrarily small nonzero coefficient is excluded.

The unique largest coordinate is `x_{p_0}=-1`, so its index is `a=p_0`. A row is active exactly when its coefficient at its last supported coordinate in this ordering is negative. Let `A` be these active rows.

If a nonempty coordinate set `C` meets each active support either in the whole support or not at all, then every active row annihilates `1_C`: each such row is zero-sum. For all sufficiently small real `t`, moving `x` to `x+t*1_C` leaves all active feature values unchanged, keeps all inactive features zero, and keeps `a` the unique maximum. Applying (1) gives

```
sum_{i in C} ell_i = 1 if a in C, and 0 otherwise.                 (3)
```

In particular each connected component of the active-support hypergraph supplies an equation (3). These equations depend only on the supports, coefficient signs, and coordinate ordering; they do not depend on coefficient magnitudes.

## Complete finite exclusion and independent arithmetic check

A nonzero zero-sum row on a two-element support has two possible coefficient-sign patterns, and on a three-element support it has six. Thus the three families have respectively `32`, `96`, and `288` sign classes, for a total of `416`. Every real zero-sum row with the stated exact support falls into one class.

The producer enumerates only the `5!=120` coordinate orderings, obtains equations (3), and records an inconsistent rational combination for every coefficient-sign class. The certificate contains 955 equations in total. Every contradiction uses only two, three, or four equations: 300 classes use two, 109 use three, and seven use four.

The independent checker does not import the producer and does not solve a linear system. It:

1. Exhaustively checks support-family coverage as above.
2. Independently enumerates all 416 coefficient-sign classes and checks exactly one certificate for each.
3. Checks the priority permutation, all-negative coordinate signs, active rows from (2), and unique maximum.
4. Checks that every recorded set `C` contains or avoids each active support, so (3) follows without trusting the producer's connected-component calculation.
5. Adds the recorded rational multiples exactly, verifying zero coefficient on every `ell_i` but nonzero right side.

Thus all 416 classes violate (1). Combined with C3/C4 this proves that a singleton `J+` or `J-` requires `|J0|>=6`.

## Width consequences

Already `|J0|>=5`, and both signed classes are nonempty. If `h1<=7`, the only remaining possibility is `( |J+|, |J-|, |J0| )=(1,1,5)`, excluded above. Thus `h1>=8`.

If `h1=8` and `|J0|=5`, the two signed classes have total size three, so one is a singleton, again excluded. Therefore `h1=8` forces `(1,1,6)`. The existing Lean theorem `ZNet.second_width_half_succ` then gives `N+2<=2*h2`, so at `N=5` one has `h2>=4`. Together with the established unrestricted `h2>=3`, this gives total width at least twelve.

The initial, weaker observation `h1=7 => h2>=4` is superseded: first width seven is impossible for every second width.

## Reproduction and trust boundary

Run from the repository root; Python's standard library is sufficient:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 120s python3 research/sN/frontierN/overnight_general_flags.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 120s python3 research/sN/frontierN/overnight_general_check.py
```

The simplified producer took 0.34 seconds and the independent checker 0.026 seconds in this run. Both exited zero. The scripts use one thread and small memory; no floating-point decision, optimizer, sampling filter, or modular rank assertion is used. The producer and checker JSON/log files are adjacent to this note. The checker records the SHA-256 of the complete certificate.

The discarded larger flag family also passed; `overnight_general_simplify.py/json/log` records the reduction to all-negative flags. Positive flags alone leave four sign classes of F2 and 36 of F3, so the positive-only shortcut is insufficient for this component condition.

This is an exact finite certificate combined with a written mathematical reduction, not yet a kernel-checked Lean theorem. A Lean integration would formalize the leading-sign lemma and implication (1) => (3), import the existing support/translation reductions, and check the small rational contradictions plus finite coverage.

The analytic implication (1) => (3) has now been checked in the owned scratch leaf `overnight_general_bridge.lean`: the general `feature_fiber_slope` theorem and its `component_equation` corollary compile under Lean 4.4.0 with only `propext`, `Classical.choice`, and `Quot.sound`. This is partial formalization, not a Lean claim for `h1>=8`. Reproduce with `lake env lean -j1 research/sN/frontierN/overnight_general_bridge.lean`.

## Subsequent unrestricted second-width result

The first-width certificate alone does not prove `h2>=4` independently of `h1`. The equality configuration for `h2=3` has one positive-slope second neuron at positive infinity, a different positive-slope neuron at negative infinity, and one neuron with zero slope at both ends. The earlier kernel-only cancellation argument left this open. The new transverse positivity argument in `overnight_general_second_width.md` closes it: the last neuron's preactivation has uniform sign on that kernel, so the restricted maximum is one-hidden-layer and violates the max/min subspace dimension bound. Both parent and independent fixed-layer agent reviewed this separate argument successfully.
