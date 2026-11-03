# Independent audit: convex-or-concave second preactivations require width n

Status: **mathematical audit passed**, 3 November 2026. No new Lean
verification is claimed here. This corollary is conditional on the already
audited mathematical convex-core bound in
`CONVEX_CORE_LINEAR_BOUND_AUDIT.md`.

## Statement

Let n>=3. An ordinary two-hidden-layer ReLU network computing MAX_n on
all real inputs, with arbitrary real weights and biases, must have at
least n second hidden neurons if **each original second preactivation**
is globally convex or globally concave as a function of the input.

The first hidden width is unrestricted. The condition concerns the whole
preactivation function, not individual coefficients and not a selected
activation cell. The result is not an unrestricted width lower bound:
general shallow preactivations may be neither convex nor concave.

The absence of an output skip is essential to the counting argument.
Zero output coefficients and zero neurons are permitted and are counted.

## Recession and notation

Homogeneous recession removes all biases at unchanged physical widths.
For each second preactivation, `g_infty(x)=lim_(t->infty) g(t*x)/t` is a
finite homogeneous shallow function. It retains convexity or concavity,
since it is a pointwise finite limit of functions of the same curvature
class. The resulting identity is

```
MAX_n(x)=sum_(j<m) d_j*sigma(g_j(x)).
```

Put `v=(1,...,1)` and use a positive parameter t at both tails:

```
g_j(x+t*v)=t*a_j^+ + b_j^+(x),
g_j(x-t*v)=t*a_j^- + b_j^-(x),
```

for all sufficiently large t for each fixed x. Here

```
a_j^+=g_j(v),       b_j^+=(g_j)'_v,
a_j^-=g_j(-v),      b_j^-=(g_j)'_(-v).
```

Each b is homogeneous shallow, with the same convex-or-concave type as
its parent. This is the exact eventual formula for finite piecewise-linear
shallow functions, not an approximation.

## Counting zero slopes

The slope identities are

```
sum_j d_j*sigma(a_j^+)=1,
sum_j d_j*sigma(a_j^-)=-1.
```

At either tail, the zero-slope terms remain folded shallow cores; positive
slope terms enter the shallow remainder, and negative slope terms vanish.
The convex-core bound says at least n-2 indices have zero slope at each
tail. Each slope identity also requires at least one positive-slope term.
Consequently m>=n-1.

Suppose m=n-1. There is exactly one index p with nonzero positive-tail
slope, and exactly one index q with nonzero negative-tail slope. They
must be passing terms:

```
a_p^+>0, d_p>0;       a_q^->0, d_q<0.
```

In particular p and q are distinct. Their other slopes are zero. Every
one of the remaining n-3 cores satisfies `g_j(v)=g_j(-v)=0`.

A homogeneous convex function vanishing at v and -v is invariant under
translation by v: apply subadditivity in both directions. For a concave
function apply this fact to its negative. Thus the common n-3 cores are
translation invariant, and their contribution

```
H(x)=sum_(j notin {p,q}) d_j*sigma(g_j(x))
```

is identical in both tail identities.

## The two exceptional gates cannot supply an extra folded core

Scale by positive numbers and write

```
P=d_p*g_p,       Q=-d_q*g_q.
```

Their contributions are sigma(P) and -sigma(Q), respectively. Their
positive/negative tail slopes are `(1,0)` and `(0,1)`. Use Pplus, Pminus,
Qplus, Qminus for their four intercept functions. The exact intercept
identities are

```
MAX_n = Pplus-sigma(Qplus)+H,
MAX_n = sigma(Pminus)-Qminus+H.
```

For every homogeneous shallow function, the difference between its two
intercepts is linear. Explicitly, if

```
g(x)=a.x+sum_r c_r*sigma(w_r.x),
```

the invariant first rows `w_r.v=0` contribute the same ReLU at both ends,
and cancel in the difference. The other rows contribute linear functions:

```
bplus(x)-bminus(x)
 =sum_(w_r.v>0) c_r*(w_r.x)
  -sum_(w_r.v<0) c_r*(w_r.x).
```

Subtract the two intercept identities. The linear function

```
ell=(Pplus-Pminus)+(Qminus-Qplus)
```

satisfies

```
ell(x)=sigma(-Pminus(x))+sigma(-Qplus(x))>=0
```

on the entire real vector space. A globally nonnegative linear function
is zero, by comparing x and -x. Both nonnegative summands therefore vanish,
so Pminus>=0 and Qplus>=0 everywhere.

The positive-tail identity consequently reduces to

```
MAX_n=(Pplus-Qplus)+H.
```

The parenthesized expression is shallow. H contains just n-3 folded
convex-or-concave shallow cores, contradicting the n-2 convex-core bound.
Thus m=n-1 is impossible, and m>=n follows.

## Audit checks

* Both tail expansions use t>0, so the target negative-tail slope is -1.
  This fixes the output-sign distinction p!=q without an orientation guess.
* The n-2 lower bound applies to all zero-slope intercept cores because
  directional derivatives preserve the curvature class and shallowness.
* At equality m=n-1 there cannot be an additional inactive nonzero-slope
  gate: the zero-slope count leaves exactly one nonzero slot, occupied by
  the required passer.
* The common cores are actual original homogeneous functions at both
  tails. Their equality is proved from convexity/concavity and the two
  diagonal zeros, rather than assuming an absent carrier shift.
* The intercept difference is linear even with arbitrary signed first
  coefficients and arbitrary first directions. Invariant ReLUs cancel.
* Normalizing P and Q uses positive factors, and hence preserves their
  curvature class. No first-layer feature is silently added to a physical
  width count.
* The final shallow remainder is free only when invoking the already
  proved residual-core theorem, whose statement explicitly allows it.

For MAX5 this excludes physical second width four throughout the class
where every second preactivation is convex or concave. It leaves the
unrestricted width-four problem open and forces any such hypothetical
network to contain a genuinely nonconvex, nonconcave second preactivation.
