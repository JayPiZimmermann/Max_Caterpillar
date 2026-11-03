# Sharp falling-support half restriction

The interference estimates charge the fourth falling factorial `(s)_4`,
not the fourth power `s^4`. Keeping that distinction improves the support
budget for one actual normalized restriction from `81 h1 / 4` to
`105 h1 / 16`. Original first and second hidden index types are preserved.

The same selected model can also satisfy `M <= h1 / 8`, where `M` counts
first hidden rows of support at least three. Thus this improves both budgets
simultaneously; they are not obtained from two different restrictions.

The proof pairs coordinates and chooses one endpoint independently from
each pair. A support of cardinality `s` survives in at most a `2^(-s)`
fraction of selectors. The sharp scalar inequality is

    16 (s)_4 <= 105 2^s,

with equality at `s=7,8`. For simultaneous control, use the integer charge

    w(s) = max(105, 2 (s)_4) if s>=3, and 0 otherwise.

It satisfies `8 w(s) <= 105 2^s`, with additional equality at `s=3`.
One selector has `8 sum w(s) <= 105 h1`. Since `w` dominates twice the
fourth falling factorial and 105 times the non-braid indicator, both claimed
budgets follow. Embedding `2n` coordinates first handles odd ambient size and
every `2n <= N`. Existing exact localization supplies the actual same-width
network, including its linear skips and arbitrary signed weights.

The sharpness assertions concern these uniform scalar dyadic envelopes.
They do not assert optimality of any MAX-network lower-bound constant.

The exact expanded model statement and small/boundary controls are in
`FallingCheck.lean`. Reproduce the isolated source-bound verification with:

```sh
python3 research/sN/overnight_20261103/constants/falling_recheck.py --run
```

These are isolated research leaves. A numerical second-hidden-width bound
requires the separate coverage, survival, actual-network, and arithmetic
assembly using these budgets.
