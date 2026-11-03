# Independent audit: at least n-2 convex-or-concave shallow cores

Status: **mathematical audit passed**, 3 November 2026. This proof replaces
the earlier special two-core convex-cover argument. No new Lean verification
is claimed in this note.

## Exact statement and scope

Let n>=3. Suppose that, on all of R^n,

```
MAX_n(x)=R(x)+sum_(j<K) d_j*sigma(g_j(x)),
```

where R and every g_j are finite affine shallow ReLU functions, the d_j
are arbitrary real numbers, and each g_j is globally convex or globally
concave. Then K>=n-2.

The first hidden width, directions, affine linear terms, and all biases
are unrestricted. The cores may initially use different dictionaries;
their union is finite. The bound counts the displayed folded cores with
a free shallow remainder. It must not be converted into a physical second
hidden-layer width bound without the appropriate reduction of that network.

Zero coefficients and zero cores are allowed. In particular zero-core
padding is valid when proving the bound by contradiction.

## Complementation preserves the model

For a concave core use

```
sigma(g)=g+sigma(-g).
```

The new core -g is convex. The term d_j*g is absorbed into R, which remains
a finite affine shallow function for every sign of d_j. After these exact
rewrites all cores are convex. No recession, bias removal, or normalization
of first directions is needed.

## Directional derivatives preserve every needed hypothesis

For a finite affine shallow function

```
S(x)=a.x+b+sum_r c_r*sigma(w_r.x+b_r),
```

its one-sided directional derivative at any point q is

```
S'_q(y)=a.y
        +sum_(w_r.q+b_r>0) c_r*(w_r.y)
        +sum_(w_r.q+b_r=0) c_r*sigma(w_r.y).
```

It is a finite homogeneous shallow function on the entire direction
space. This formula includes zero rows, zero coefficients, and first gates
on their boundaries. If S is convex, S'_q is convex: it is the pointwise
limit as t decreases to zero of the convex functions
`y |-> (S(q+t*y)-S(q))/t`. All these finite directional limits exist by
the displayed shallow formula.

For each outer fold the derivative is exactly

```
(sigma(g))'_q = g'_q       if g(q)>0,
(sigma(g))'_q = 0          if g(q)<0,
(sigma(g))'_q = sigma(g'_q) if g(q)=0.
```

Thus every nonzero-valued core at q disappears from the folded-core count,
and contributes at most a shallow term to the remainder. Every retained
core is still a convex homogeneous shallow function. Restriction to a
linear subspace preserves these properties.

## Induction

The base n=3, K=0 says that MAX3 is not affine shallow. Taking its germ at
the origin would give a homogeneous shallow representation. The odd part
of any homogeneous shallow function is linear, whereas MAX3+MIN3 has
value 1 at each of the three coordinate vectors and value 2 at their sum.
This contradicts linearity.

Suppose the theorem is known for n-1 and that a counterexample exists at n.
Pad by zero cores so K=n-3. Fix any point q at which exactly n-1 coordinates
tie for the maximum, with the excluded coordinate strictly smaller.

If any g_j(q) were nonzero, the directional identity above would have at
most K-1=n-4 folded cores. The target directional germ is the maximum of
the n-1 tied coordinate directions. Set the excluded direction coordinate
to zero. This yields an exact representation of MAX_(n-1) by a shallow
remainder and at most n-4 convex shallow cores, contradicting the inductive
bound `(n-1)-2=n-3`.

Therefore **every** core vanishes at **every** such (n-1)-way top tie.
This conclusion is stronger than the usual disjunction that at least one
core vanishes at a triple tie; the near-threshold core count is essential.

## Convexity turns those contact zeros into global inactivity

Fix arbitrary x in R^n. Choose `M=max_i x_i+1` and put

```
s=sum_i(M-x_i)>0,
v_i=M*1-s*e_i,
lambda_i=(M-x_i)/s.
```

Every v_i has exactly n-1 maximizing coordinates, so every g_j(v_i)=0.
Moreover lambda_i>0, their sum is one, and

```
sum_i lambda_i*v_i=x.
```

Convexity gives, separately for every core,

```
g_j(x)<=sum_i lambda_i*g_j(v_i)=0.
```

Since x was arbitrary, every folded term sigma(g_j) vanishes identically.
The original identity reduces to MAX_n=R. This is impossible for n>=3:
the linear map repeating the third coordinate in positions 3 through n
would turn it into an affine shallow MAX3 representation.

The induction proves K>=n-2.

## Audit conclusions and limits

All load-bearing steps pass independently: complementation preserves the
actual shallow class, nonzero outer gates really remove a core after taking
directional germs, convexity survives directional differentiation and
restriction, the contact simplex contains every real x, and biases require
no extra argument. Arbitrary outer signs cause no issue at any step.

For MAX5, an identity with two folded shallow cores must contain a core
that is neither convex nor concave. For MAX6, the same is true with at most
three cores. The statement is a linear lower bound within the stated
curvature class; it is not an unrestricted lower bound for arbitrary
shallow preactivations.

Compared with the earlier two-core proof, this argument removes the
two-convex-set covering lemma, complementary-halfspace classification,
translation-invariance argument, and the free-neuron theorem. The retained
ingredients are only the shallow MAX3 obstruction, directional derivatives,
finite convex combinations, and induction.
