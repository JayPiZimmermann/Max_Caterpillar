# Unrestricted second width at five inputs: structural branch

**Open target:** prove or refute that every exact two-hidden-layer ReLU
network for `max_5`, with arbitrary real first-layer rows and biases and no
skip connections, has second width at least six. The known `(10,6)`
construction would then match the unrestricted second-width bound.

**Current evidence:** exact structural lemmas and five globally checked
scalar identities, including two-winner rigidity and obstructions to
several selector flattenings. None proves the target. Bounded construction probes are
paused while this structural branch is explored. The existing general
Lean lower bound remains four. A separate first-width classification and
finite certificate prove that first width eight requires second width at
least seven; that does not settle the unrestricted second width.

## 1. Translation tails and the missing extra neuron

Homogeneity removes biases. Write the first-layer rows as `a_j`, the
second-layer coefficients as `W_kj`, and output coefficients as `d_k`.
Let `c_j=a_j dot 1`, and define

```
t_k^+ = sum_(c_j>0) W_kj c_j,
t_k^- = sum_(c_j<0) W_kj (-c_j),
G_k^+(x) = sum_(c_j>0) W_kj (a_j dot x)
             + sum_(c_j=0) W_kj sigma(a_j dot x),
G_k^-(x) = sum_(c_j<0) W_kj (a_j dot x)
             + sum_(c_j=0) W_kj sigma(a_j dot x).
```

For fixed `x`, these are the exact eventual slope and intercept at
`x+t1` and `x-t1`, respectively. Taking the constant terms gives

```
max_5(x) = sum_(t_k^+>0) d_k G_k^+(x)
               + sum_(t_k^+=0) d_k sigma(G_k^+(x)),
max_5(x) = sum_(t_k^->0) d_k G_k^-(x)
               + sum_(t_k^-=0) d_k sigma(G_k^-(x)).
```

At least one positive slope occurs at each end, since the output slopes
are `+1` and `-1`. A zero-slope preactivation is translation invariant:
`G_k^+(x+s1)=G_k^+(x)` when `t_k^+=0`, and similarly at the negative end.
Every nonzero-slope first-layer row has become linear. The remaining
first-layer functions are arbitrary invariant functions
`sigma(a dot x)` with `a dot 1=0`; there is no reason for `a` to be a
coordinate difference.

Let `k_*` be the least number of free outer ReLUs in

```
max_5 = R + sum_(i<K) d_i sigma(g_i),
```

where `R` and the invariant `g_i` are arbitrary homogeneous shallow
functions, and `R(x+s1)=R(x)+s`. Then a single translation end proves
only

```
h2 >= k_* + 1.
```

In particular, proving `k_*>=4` would directly give `h2>=5`, not six.
If `h2=5`, that result would force a unique positive-slope neuron at each
end, with different indices and opposite output signs, leaving three
common zero-slope neurons. However,

```
G_k^+(x)-G_k^-(x)
 = [sum_(c_j>0) W_kj a_j - sum_(c_j<0) W_kj a_j] dot x
 = delta_k dot x.
```

For a common zero-slope neuron, `delta_k dot 1=0`, but `delta_k` need
not be zero. Multiple positive- or negative-slope first-layer rows can
cancel their diagonal slopes without cancelling their transverse linear
parts. Thus the fixed-layer `+2` argument does not automatically extend.
A proof of `k_*>=4` and a separate bridge excluding these shifted tail
intercepts are both sufficient; neither is presently supplied here.

## 2. Odd parts do not by themselves reach the desired bound

Every homogeneous shallow function satisfies

```
g(x)-g(-x)=linear(x).
```

In a free representation with `K` outer terms, intersecting the kernels
of these `K` linear odd parts makes every outer term even. Therefore
`max_5(x)+min_5(x)` must be linear on that intersection. The known
max/min subspace bound yields only `K>=2`. In the four-dimensional
translation quotient, three kernels can meet in a line, and every odd
homogeneous function is already linear on a line. A stronger argument
must use curvature or compatibility away from that common kernel.

Equivalently, since `sigma(g)=(g+abs(g))/2`, the core question is whether
the simplex support function modulo the vector space of shallow
functions is a signed sum of three absolute values of shallow functions.
This reformulation does not impose convexity on the inner functions.

## 3. What a non-braid first-layer wall forces

Consider a core representation with three free outer neurons. Consolidate
all first-layer functions with the same unoriented hyperplane into one
`sigma(h)` term, absorbing opposite orientations into linear terms.
Suppose `H=ker(h)` is not a coordinate-equality wall of the target.
Let `r` be the coefficient of this term in the shallow remainder and
`w_i` its coefficient in preactivation `g_i`.

On a relatively open cell of `H` avoiding other first-layer walls and
all outer zero sets, smoothness of the target across `H` gives

```
r + sum_(i=1)^3 alpha_i epsilon_i = 0,
alpha_i=d_i w_i,
epsilon_i=1_(g_i>0).
```

Thus the activation vectors realized on `H` lie in an affine plane
section of the Boolean cube. If all three `alpha_i` are nonzero, that
section contains at most three cube vertices. No two allowed vertices
can differ in a single coordinate. Consequently every change of
activation across a generic boundary in `H` must involve at least two
simultaneous outer zeros.

If a preactivation vanishes identically on an open cell of `H`, this
argument does not apply on that cell: the outer ReLU itself folds across
`H`, and its normal contributions need separate treatment. If some
`alpha_i` vanish, the corresponding coordinate is unconstrained and the
lower-dimensional cube cases must also be retained.

The three-vertex case cannot simply be discarded. For three linear
forms `a,b,c`, the shallow functions

```
A=a-max(b,c), B=b-max(a,c), C=c-max(a,b)
```

have exactly one positive value whenever the maximum of `a,b,c` is
unique. They realize a genuine three-way selector. Thus smoothness does
not force the offending first-layer coefficient to vanish.

## 4. An exact selector identity

For any real `a,b,c,h`, put `s=sigma(h)` and

```
A=a-max(b,c),
B=b-max(a,c),
C=c-max(a,b),
R=max(a,c)+max(b,c)-max(a,b)-s.
```

Then

```
R + sigma(A+s) + sigma(B+s) - sigma(C-s)
    = max(a,b,c,min(a,b)+h).                         (*)
```

All three preactivations and `R` are shallow when `a,b,c,h` are linear.
The first-layer wall `h=0` is generically absent from the output crease
set, yet its coefficient cancels through the three-way selector.

To prove (*), assume `a>=b` by symmetry. If `c<=a`, the left side reduces
to `a+sigma(s-(a-b))=max(a,b+s)`. If `c>=a`, use
`sigma(s-(c-a))-sigma((c-a)-s)=s-(c-a)` to reduce it to
`c+sigma(s-(c-b))=max(c,b+s)`. Both equal the claimed right side: when
`h<0`, replacing `s=0` by `h` cannot affect the maximum.

This is not a five-input maximum counterexample. The five linear forms
`a,b,c,a+h,b+h` satisfy a relation, and the last two appear through their
minimum. The identity does show that a removability or surgery lemma
for non-braid first-layer walls requires more than counting activation
patterns. It is a possible building block for either a counterexample
or a classification of the remaining selector case.

## 5. The natural five-input substitution and its exact obstruction

In (*), set

```
m=min(a,b), M=max(a,b), D=max(d,e), h=D-m.
```

The target becomes exactly `max(a,b,c,d,e)`. But `h` is shallow rather
than linear, so the common `sigma(h)` inside all three preactivations
would add a third hidden layer.

Replace that common `sigma(h)` by `h` itself. The result is

```
max(a,b,c,d,e) + E,
E=min(sigma(2m-M-D), sigma(m-c)).
```

This follows directly from the two cases in the proof of (*). The error
is supported where `a,b` are the two largest inputs, with their gap
small enough that `D<2m-M`. Thus the naive flattening is not an identity.

The error is repaired exactly by replacing the negative preactivation
`c-M-D+m` by

```
G3=max(c,m)-M-D+m.
```

Writing

```
G1=a-max(b,c)+D-m,
G2=b-max(a,c)+D-m,
R=max(a,c)+max(b,c)-M-D+m,
```

gives the exact identity

```
max_5 = R+sigma(G1)+sigma(G2)-sigma(G3),
G3=-max(G1,G2).
```

Here `G1,G2,R` are shallow, while `G3` is not. To verify the identity,
assume `a>=b`. Then `G1>=G2`, `R+G1=max(a,c)`, and
`G2=D-max(a,c)`. Use `sigma(G1)-sigma(-G1)=G1`.

There is a stronger obstruction than the fact that this displayed
`G3` is not shallow: **no shallow function `g` can satisfy
`sigma(g)=sigma(G3)` globally.** This statement allows arbitrary first
hidden layer directions and widths.

Indeed, along the hyperplane `a=b=z`, put `w=a-b` and keep the average
`z=(a+b)/2` fixed. In the relatively open region `c<z` and `D<z`,

```
G3=z-D-(3/2)|w|
```

near the hyperplane, so the derivative in `w` has jump `-3`. In the
relatively open region `c>max(z,D)`,

```
G3=c-D-|w|,
```

and the derivative jump is `-2`. In both regions `G3` is strictly
positive near the hyperplane. If `sigma(g)=sigma(G3)`, then `g=G3`
there. A homogeneous shallow function has one constant normal jump
coefficient along a fixed hyperplane away from its other first-layer
hyperplanes. Finitely many other hyperplanes cannot cover either open
region. The two different coefficients give a contradiction.

Consequently one cannot fix this construction merely by replacing the
negative preactivation with another shallow function while retaining the
two positive preactivations and the remainder. Any successful three-unit
flattening must change them jointly, or use a different identity.

A single exploratory joint-pattern test was also performed:
`overnight_fixed_selector_flatten.py`. It frees all three preactivations
and the shallow remainder in a 33-feature invariant first-layer span,
including the hyperplanes containing every zero facet of the corrected
pattern and those of the known four-term control. The arrangement has
542 rays. The control passes; the 802 equalities and 1366 inequalities
for the three-term pattern are reported infeasible by HiGHS in about one
second. This is a solver diagnostic for that fixed span and activation
pattern, not an independently certified lower bound and not an exclusion
of arbitrary extra first-layer hyperplanes.

## 6. Two-winner rigidity for arbitrary shallow functions

For distinct input labels `i,j`, let

```
C_i={x : x_i>x_k for every k!=i},
C_j={x : x_j>x_k for every k!=j}.
```

**Lemma.** A homogeneous shallow function that vanishes on both `C_i`
and `C_j` is identically zero. There is no restriction on its finite
first-layer width or its real first-layer directions.

Consolidate its first-layer functions by unoriented hyperplane, absorbing
reversed orientations into the linear part. Any hyperplane meeting one
of the open cones has zero coefficient: choose a point of that
intersection away from all other first-layer hyperplanes, where the
function is locally zero on both sides.

It remains to classify hyperplanes avoiding both open cones. A nonzero
common-shift slope makes a hyperplane meet every `C_i`, since common
translation preserves the cone. Thus its normal `alpha` has zero sum.
For a hyperplane to avoid `C_i`, either `alpha_i>=0` and all other
coordinates are nonpositive, or the reversed inequalities hold. This
follows by writing `alpha dot x=sum_(k!=i) alpha_k(x_k-x_i)` and varying
all the negative differences independently. Imposing the corresponding
condition for `C_j` leaves only a multiple of `e_i-e_j`. Hence the
shallow function is linear plus a multiple of `sigma(x_i-x_j)`.
Vanishing on open sets on both sides forces that coefficient and the
linear part to be zero.

In particular, two shallow functions agreeing on both winner cones
agree everywhere. If one shallow function agrees with `max_N` on
`C_i union C_j`, it must equal `max(x_i,x_j)` globally. It cannot also
agree with `max_N` on a third winner cone.

### No common shallow replacement in the selector identity

Return to the five-input substitution in the previous section. Allow
an arbitrary continuous shallow function `s(a,b,c,d,e)` to replace the
common nested `sigma(h)` everywhere, keeping the formula's dependence on
that common argument. There is no such replacement computing `max_5`.

On `C_d`, the target is `d>max(a,b,c)`. The scalar selector expression at
`s=0` is `max(a,b,c)`, so exactness would force `s` to be nonzero
throughout `C_d`. This cone is connected. In its nonempty subregion
`c>=min(a,b)`, the scalar expression for every real `s` is
`max(a,b,c,min(a,b)+s)`, forcing `s=d-min(a,b)>0`. Continuity therefore
forces `s>0` on all of `C_d`. The positive-argument selector identity
then gives `s=d-min(a,b)=h` throughout that cone. The same argument
applies on `C_e`.

The function `h=max(d,e)-min(a,b)` is itself shallow. Thus `s-h` is
shallow and vanishes on `C_d union C_e`; the lemma forces `s=h`
everywhere. The strictly positive error in the previous section gives
a contradiction. For example, at

```
(a,b,c,d,e)=(0,0,-2,-1,-1)
```

the naive common replacement gives one while `max_5` is zero.

The continuity step is essential: in part of a winner cone, the scalar
selector expression also has a negative-argument branch with the same
value. Pointwise comparison alone would not force `s=h`.

This rules out every common shallow substitution, not a fully asymmetric
redefinition of all three preactivations and the remainder. The general
three-outer-neuron problem and the separate translation-tail bridge
remain open.

## 7. A second common-deformation mechanism also fails

For all real `g,s`,

```
sigma(g+s)+sigma(g-s)-sigma(g)
    = sigma(g)+sigma(abs(s)-abs(g)).
```

This gives a natural three-neuron splitting of a one-neuron construction.
Let `A=max(a,b)`, `B=max(c,d)`, `g=A-B`, so
`B+sigma(g)=max(a,b,c,d)`. Adding a fifth input `e` by the splitting
formula would require, on the open cone where `e` is uniquely largest,

```
abs(s)=e-min(A,B).
```

No continuous homogeneous shallow `s` can satisfy this requirement.
The right side is strictly positive there, so the sign of `s` is constant
on that connected cone. For fixed `a,b,c,d`, send `e` to positive
infinity. The eventual slope and intercept of a shallow function remain
linear plus shallow functions in the other four inputs. Consequently
`min(max(a,b),max(c,d))` would have to be shallow.

It is not shallow: along `a=b=z`, its normal derivative jump is zero
where `max(c,d)<z`, and one where `max(c,d)>z`. The same constant-jump
argument as above gives a contradiction.

This excludes the shared symmetric splitting mechanism, even with
arbitrary first-layer directions and width. It does not exclude three
outer neurons whose preactivations change independently.


## Reproduction and evidence boundary

The standard-library checker `overnight_fixed_selector_control.py`
independently verifies five identities on their complete central
hyperplane arrangements. Its expression tree recursively overapproximates
all possible linear gradients and includes every branch-switching
hyperplane. Coordinate hyperplanes ensure pointed cones. Intersections
of `d-1` independent hyperplanes include every extreme ray, and exact
rational equality on all rays proves the identities globally.

```
python3 overnight_fixed_selector_control.py
```

The adjacent JSON and log record the exact checks and the two distinct
normal jumps. This is an exact finite certificate, not Lean verification.
The two-winner rigidity lemma was independently reviewed by the general
proof agent, using the normal-cone argument rather than these finite
controls. Its proof and the translation-tail bridge are mathematical
arguments in this note, not claims established by the identity checker.

On the naive substitution's positive-error region, both positive
preactivations are negative. Altering only either or both positive units
cannot reduce the error, because their ReLU outputs are already zero.
Altering only the remainder is also impossible: the nonzero error
vanishes on both the `d`- and `e`-winner cones, so two-winner rigidity
prevents it from being shallow. Together with the negative-unit and
common-substitution obstructions above, this sharply limits local
repairs of this particular identity. It does not classify all possible
asymmetric three-neuron constructions.

`overnight_fixed_unrestricted_manifest.json` freezes this note and the
exact identity controls. The diagnostic LP named in section5 is not a
logical dependency and is not promoted to a certified theorem. No broad
fixed-pattern search is running as part of this structural checkpoint.
