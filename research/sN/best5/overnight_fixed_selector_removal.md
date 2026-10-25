# Arbitrary first hidden layer: the corrected selector pattern is impossible

**Result:** the corrected selector activation pattern below cannot compute
`max_5` with three free outer ReLUs and a shallow remainder, even when all
first-layer directions, widths, real coefficients, and the remainder are
changed jointly. This is a restriction on one activation pattern, not a
proof that every three-neuron representation is impossible. The
unrestricted second-hidden-layer lower bound six remains open.

The proof eliminates every non-braid first-layer wall, then uses a
34-equation exact rational contradiction. The finite checker is independent
of the search and uses only Python's standard library. The analytic wall
elimination is a separate mathematical bridge; this result is not Lean
verified.

## Model and pattern

For input `(a,b,c,d,e)`, set

```
m=min(a,b), M=max(a,b), D=max(d,e),
G1=a-max(b,c)+D-m,
G2=b-max(a,c)+D-m,
G3=max(c,m)-M-D+m=-max(G1,G2).
```

A *shallow* function means a finite real linear combination of linear
functions and functions `sigma(linear)`. Suppose shallow functions
`R,g1,g2,g3` and arbitrary real output coefficients `d1,d2,d3` satisfy

```
max(a,b,c,d,e)=R+sum_i d_i sigma(g_i),
G_i>0 implies g_i>=0,
G_i<0 implies g_i<=0.                              (1)
```

The sign conditions are weak and allow every degenerate or zero neuron.
They preserve the corrected selector's activation regions, while freeing
all function values and coefficients. We prove that (1) is impossible.

If `G_i(x)=0`, shift both `d,e` by a small common `t`. Then `G1,G2`
increase by `t`, and `G3` decreases by `t`. The two weak sign conditions
and continuity force `g_i(x)=0`. Thus every zero constraint used below is
a consequence of (1), rather than an extra strict-sign assumption.

Absorb the output coefficient into `H_i=d_i g_i`. On each open region
with activation vector `epsilon`, the right side of (1) is the shallow
branch `R+sum_i epsilon_i H_i`. This remains true if an actual `g_i`
vanishes on part or all of that region. Arbitrary output signs and zero
coefficients therefore require no additional cases.

## Four connected open regions

The only strict activation vectors of `(G1,G2,G3)` are

```
110, 100, 010, 001.
```

Write their open regions as `U110,U100,U010,U001`. They are nonempty and
connected:

* `U110={max(d,e)>max(a,b,c)}`. It is the union of the connected regions `d>max(a,b,c)` and
  `e>max(a,b,c)`, which have a nonempty overlap.
* On `U100`, necessarily `a>b`, and
  `max(b,c)-a+b < max(d,e) < max(a,c)`.
  The base `a>b` is connected. For fixed `a,b,c`, the fiber
  `L<max(d,e)<P` is connected; deform `(d,e)` to the continuous section
  `d=e=(L+P)/2`. Hence `U100` is connected. `U010` is symmetric.
* `U001={d<L0,e<L0}`, where
  `L0=max(c,min(a,b))-max(a,b)+min(a,b)`.
  Its fibers are open boxes and have the continuous section
  `d=e=L0-1` over the connected base `(a,b,c)`.

All four regions are invariant under common translation of all five
inputs.

## Every non-braid hyperplane meets all four regions

A linear hyperplane avoiding a connected open region has a defining
linear form of constant strict sign there. Common-translation invariance
then forces its normal to have coordinate sum zero. Reverse its sign if
needed, so it is nonnegative on the region's closure.

Consider `U100` on the subspace `a=b=0`. Its closure contains the six
vectors whose `(c,d,e)` coordinates are

```
 ±(1,1,0), ±(1,0,1), (-1,0,0), (0,-1,0).            (2)
```

Indeed, they satisfy `max(d,e)=max(0,c)`, and can be approached with
`a>b` and `max(d,e)` strictly between the two bounds above.
If `alpha` is nonnegative on this closure, the first four vectors force

```
alpha_c+alpha_d=alpha_c+alpha_e=0.
```

The last two give `alpha_c<=0` and `alpha_d<=0`, so all three
coefficients vanish. Zero total sum leaves only a multiple of `a-b`.
Therefore the only hyperplane avoiding `U100` is `a=b`; the same holds
for `U010`.

The closure of `U001` contains the same six vectors (2). Hence a normal
of constant sign there would also be a multiple of `a-b`. But both

```
(1,-1,0,-4,-4), (-1,1,0,-4,-4)
```

belong to `U001`, so that multiple must be zero. Consequently no
nonzero linear hyperplane avoids `U001`.

Finally, a hyperplane avoiding `U110` avoids both open unique-winner
cones for `d,e`. The normal-cone argument in
`overnight_fixed_unrestricted.md` shows that its normal must be a
multiple of `d-e`. This can also be checked directly: a hyperplane
avoiding a unique-winner cone has, up to sign, one nonnegative normal
coordinate at the winning label and all other coordinates nonpositive.
Imposing this for two different labels leaves just their difference.

Thus every hyperplane other than a coordinate-equality hyperplane meets
all four open activation regions.

## Wall elimination

Consolidate the first-layer functions of `R,H1,H2,H3` by their
unoriented hyperplanes. Reversing a function's orientation changes it by
a linear function, which can be absorbed into the corresponding linear
part. Fix a non-braid hyperplane `H`, and let its four scalar jump
coefficients in these shallow functions be `r,h1,h2,h3`.

In each of the four open regions, choose a point of `H` away from every
other first-layer hyperplane and every target coordinate-equality wall.
Such a point exists because `H` meets that region openly within `H`
and is distinct from all those finitely many walls. The target is
locally linear there. The appropriate shallow branch therefore has
zero normal jump, giving

```
U110: r+h1+h2=0,
U100: r+h1=0,
U010: r+h2=0,
U001: r+h3=0.
```

These equations force `r=h1=h2=h3=0`. This applies to every non-braid
first-layer wall. Hence all four functions use only linear functions
and coordinate-difference ReLUs, regardless of the original first-layer
width or directions.

This step does not assume that actual outer preactivations avoid zero on
`H`: throughout a prescribed open activation region, weak compatibility
already makes `sigma(g_i)` identically either `g_i` or zero.

## Exact contradiction in the remaining span

Restrict to `a=x0=0`. All remaining shallow functions belong to the
14-dimensional span with ordered features

```
sigma(x_i-x0), i=1,...,4;
sigma(x_i-x_j), 0<=i<j<=4.
```

The two orientations based at `x0` also span every linear function on
this hyperplane. Thus there are 56 unrestricted real coefficient
parameters for the remainder and three shallow blocks. The checker
negates the third unknown block by convention; this invertible change
of variables does not restrict output signs.

At a point `x`, impose the value equation from the prescribed active
branch. If `G_i(x)=0`, also impose the forced zero equation on the
corresponding block. The certificate
`overnight_fixed_selector_pair_certificate.json` lists 34 such original
equations with integer multipliers. Their left sides sum identically to
zero in all 56 parameters, while their right sides sum to one.

The standard-library checker regenerates every equation directly from
its input point and the 14 feature functions. It recomputes
`G3=-max(G1,G2)` independently of the producer's displayed formula,
checks every declared zero, and verifies the rational sum `0=1`.
No numerical LP verdict, rank computation, inferred sign feasibility,
or generated row matrix is trusted.

```
python3 overnight_fixed_selector_pair_verify.py
```

The adjacent receipt reports
`INDEPENDENT_EXACT_SELECTOR_PAIR_PATTERN_EXCLUSION_PASS`.
Together with wall elimination, this proves the arbitrary-first-layer
pattern exclusion stated above.

## What remains open

A different asymmetric three-neuron activation pattern may evade this
argument. The wall-intersection property is specific to the four regions
above. It cannot be assumed for arbitrary shallow preactivations.
Moreover, excluding all three-free-neuron cores would still leave the
translation-tail bridge discussed in `overnight_fixed_unrestricted.md`
before it implied an unrestricted total second width of six.
