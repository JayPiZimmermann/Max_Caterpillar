# Audit: matching roots plus one genuine nonroot

Status: 31 October 2026. Independent mathematical audit PASS of the
local extremality argument proposed by `max5_exact_shared_positive`,
with the zero-plane routing step strengthened below. No Lean claim.

## Statement

Suppose

```
Max4=R+ReLU(g)+ReLU(h),
```

where R,g,h are homogeneous shallow functions with arbitrary linear
terms and only the nonlinear hyperplanes

```
x0=x1, x2=x3, H=0,
```

where H is a genuine invariant nonroot linear form. Every outer fold
that is not itself shallow must be a nonnegative multiple of one of
the two orientations of the canonical comparator

```
G=max(x0,x1)-max(x2,x3).
```

More precisely, if one core has nonzero H curvature, its folded
function is shallow and the other core is exactly G or -G after
absorbing the positive output magnitude. If neither uses H, the
genuine comparator folds have absolute coefficients summing to one;
any remaining folded term is shallow.

## 1. A nonroot crosses a missing facet

Write the coefficients of H as w0,w1,w2,w3 with sum zero. On the open
cross facet ij, with i in {0,1} and j in {2,3}, H crosses the facet
interior exactly when its two outside coefficients have opposite
strict signs. If no such cross-block pair has opposite signs, all
nonzero positive and negative coefficients lie in one block. The other
block is zero, so H is proportional to one of the two existing roots.
This contradicts the nonroot hypothesis.

On an open cross facet the two matching-root preactivations are strict.
Thus at a generic H/facet intersection there is only one first singular
hyperplane, H itself.

## 2. A core using H cannot carry that crossed facet

Let a positive core carry a nonempty open patch of a target facet on
one side of H, so its affine form there is a nonzero multiple of the
target normal. Across H its affine form changes by c*H, where c is
its nonzero consolidated H curvature. The resulting zero plane is
neither the target facet nor H. It crosses an open region where the
target and the shallow remainder are affine. Its positive outer
curvature cannot cancel against another positive fold.

An identically zero affine form on the other side is also impossible:
it would require a nonzero multiple of the target normal to be
proportional to H. This handles zero-form plateaus explicitly.

Consequently both cores cannot have nonzero H curvature. On the crossed
target facet at least one positive core must carry the unit target
crease, so one core, say h, has zero H curvature and carries a target
facet.

## 3. The two-root core is globally canonical

Use invariant coordinates

```
a=x0-x1, b=x2-x3, z=x1-x3,
G=z+ReLU(a)-ReLU(b).
```

A nonzero diagonal slope of a positive core would create positive
curvature along a common-translation line, whereas the target and
shallow remainder are affine there. Thus both cores are invariant.

Since h carries a cross facet, its z coefficient k is nonzero.
Its normalized affine forms n=h/k on the four strict (a,b) quadrants
all have z coefficient one. The target zero forms are

```
C++=z+a-b, C+-=z+a, C-+=z-b, C--=z.
```

Every zero of h away from the first hyperplanes must be a target zero,
because positive outer curvature cannot cancel there. On a fixed
quadrant its zero graph covers all (a,b) values in that quadrant.
The graph must therefore equal either the target plane C or the first
plane H, whenever H has nonzero z coefficient. A union of two distinct
planes cannot cover a relatively open subset of a third plane. If
H has zero z coefficient, it cannot be the graph of h, and only C is
possible.

Assume H has nonzero z coefficient and normalize it to H0 with z
coefficient one. Let S be the quadrants where n equals H0 instead of
C. Because h uses only two first roots,

```
n+++n--=n+-+n-+.
```

* If S has one or three quadrants, this equation forces H0 to equal
  one of the root forms C, contrary to the hypothesis.
* If S consists of two adjacent quadrants, the equation forces a or b
  to vanish as a linear form, which is impossible.
* If S consists of two diagonal quadrants, it forces
  `H0=z+(a-b)/2`. This violates continuity across a quadrant boundary.
  For example, for S={++,--}, the values at a=0,b>0 would be
  z-b/2 from ++ and z-b from -+. The other diagonal is analogous.
* If S contains all four quadrants, h=k*H0 globally and carries no
  open cross target facet, contradicting its selection.

Hence S is empty, and h=k*G globally. This is the essential corrected
step: merely asserting that a constant z slope makes h canonical would
overlook possible zero planes on H. The finite routing argument excludes
them, including the diagonal replacement pattern.

## 4. Curvature fixes the magnitude and removes the other fold

If g uses H, it cannot carry the crossed facet from Section 1.
Therefore h alone supplies the target jump there, giving |k|=1.
For k=1, `Max4-ReLU(h)=max(x2,x3)`; for k=-1 the difference is
`max(x0,x1)`. Both are shallow. The exact identity then gives

```
ReLU(g)=Max4-ReLU(h)-R,
```

so ReLU(g) is shallow. This conclusion follows from the identity itself;
it does not rely on the false general assertion that absence of
interior first-cell crossings alone implies shallowness.

If neither core uses H, a second genuine core carrying any target
crease is canonical by Section 3 as well. Positive target curvature
then makes the sum of their absolute comparator coefficients equal to
one. If a core carries no target crease, the remaining one has magnitude
one and the same exact subtraction shows that unused fold is shallow.

This proves the stated local extremality result.

## 5. A third coordinate root: independent audit of the extension

The root-only extension also passes audit. After relabeling within the
two matching pairs, the third distinct root can be taken as 02. Use

```
a=x0-x1, b=x2-x3, c=x0-x2,
Max4-x2=max(c,c-a,0,-b),
C=c+ReLU(-a)-ReLU(-b).
```

The three first hyperplanes are the coordinate planes a=0,b=0,c=0.
Every shallow core is a sum of three one-variable piecewise-linear
terms. Denote its six axis coefficients by a+,a-,b+,b-,c+,c-, so
on a strict orthant it is a_sign*a+b_sign*b+c_sign*c.

The target has internal first-orthant creases only in these four
orthants, with the indicated defining form:

| Orthant | Target form |
| --- | --- |
| a>0,b<0,c>0 | c+b |
| a<0,b>0,c<0 | c-a |
| a<0,b<0,c>0 | c-a+b |
| a<0,b<0,c<0 | c-a+b |

Every core crossing the interior of a first orthant must have its zero
plane equal to that target plane: the shallow remainder is affine and
all outer curvature is nonnegative there.

Suppose a core carries the first listed crease. For a nonzero k, its
coefficients satisfy a+=0 and b-=c+=k. In the third orthant, varying
b<0 and c>0 produces both signs whatever a- is, so that core necessarily
crosses. Matching the target plane forces a-=-k. In the fourth orthant,
the a and b terms have opposite signs and again force a crossing,
giving c-=k. In the second orthant the a and c terms have opposite
signs, forcing b+=0. Therefore the core is k*C globally.

Starting from the second orthant gives the same conclusion in the
reverse order. Starting in either of the last two fixes a-=-k,b-=k;
these opposite terms force a crossing in the other such orthant and
then in both first orthants, again fixing all six coefficients.

If a core crosses no first orthant, its folded function is linear on
each coordinate orthant. Continuity across a coordinate plane makes
each other coordinate's coefficient unchanged across that plane.
Thus each coefficient depends only on its own coordinate sign, and
the folded function is a sum of three one-variable hinges and a
linear function. It is shallow.

Hence every nonshallow positive fold over the three root hyperplanes
is a multiple of the same canonical comparator C. This argument works
for any finite number of positive outer folds. Their absolute comparator
coefficients sum to one by the target's unit normal jump. A repeated
third root or only two distinct roots is included by assigning zero
coefficient to an arbitrary added cross root.

Together with the three-hyperplane exclusions in
[local4_three_hyperplanes.md](local4_three_hyperplanes.md), this establishes
the complete local conclusion: with at most three nonlinear first
hyperplanes, a positive-two-core Max4 identity has a matching pair of
coordinate roots, and every genuine folded term has that pairing's
canonical comparator germ. Other folded terms are shallow and can be
absorbed into the remainder.
