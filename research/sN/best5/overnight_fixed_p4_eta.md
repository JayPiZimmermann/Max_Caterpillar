# The single-comparison-argument route to `(9,6)` fails exactly

The known four-free-term identity has the form

\[
 G_\eta=a+\sigma(\eta)-\sigma\bigl(\eta+(a+b-c-d)/2\bigr)
       +\tfrac12\sigma(b-a+d-c)+\tfrac12\sigma(b-a+c-d),
\]

where `a=sigma(u), b=sigma(v), c=sigma(s), d=sigma(t)`.
The targeted proposal was to replace only `eta` by an arbitrary linear
combination of the certified seven P4 features

\[
 z=(\sigma(u),\sigma(v),\sigma(v-u),\sigma(s),\sigma(t),
       \sigma(s-t),\sigma(v-t)).
\]

This proposal is impossible. It does not exclude other four-free-term
representations on this first layer.

Put `S=a+b,T=c+d,D=|a-b|,E=|c-d|,k=(T-S)/2`. Then

\[
 G_\eta=(S+\max(D,E))/2+\sigma(\eta)-\sigma(\eta-k).
\]

When the desired correction is strictly between its two saturation
values, this equation uniquely fixes `eta`. At the following inputs the
forced values are

| Input `(u,v,s,t)` | Forced `eta` |
|---|---:|
| `P-=(4,4,2,-1)` | -2 |
| `P0=(4,4,2,0)` | -2 |
| `P+=(4,4,2,1)` | -2 |
| `Q1=(0,3,4,5)` | 2 |
| `Q2=(0,3,4,6)` | 3 |

The feature relation is

\[
 z(P_-)+z(P_+)-2z(P_0)=z(Q_2)-z(Q_1)=(0,0,0,0,1,0,0).
\]

The first equality would force the coefficient of `sigma(t)` in `eta`
to be zero; the second would force it to be one. The standalone checker
`overnight_fixed_p4_eta_check.py` verifies the strict unsaturated cases,
the exact feature relation, and the contradictory forced values with
rational arithmetic. It imports no search producer.

The earlier producer also validated the known ten-row comparison formula
on 947 exact inputs before finding its first contradiction. This is a
positive implementation control, not part of the five-point proof.
