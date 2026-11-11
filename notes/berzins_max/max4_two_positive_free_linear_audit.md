# Audit: exact two-positive-fold extremality with all linear forms

Date: 2026-10-31. Audit target:
`max4_two_positive_free_linear_exact.py`, including its cone cover,
rational certificates, and theorem assembly.

Verdict: the exact restricted theorem is supported. The first-function
space consists of the six coordinate comparison hyperplanes and all
linear forms. No arbitrary additional non-root hyperplane is covered.

## Reduction to the nine-dimensional invariant feature space

Suppose

    Max4 = R + ReLU(g) + ReLU(h),

where all three functions are in the span of the six comparison ReLUs
and all linear forms. On any complete line in the diagonal direction,
R is affine and each folded term is convex. Their sum is affine.
Therefore each folded term is affine on that line. A ReLU of a linear
function with nonzero slope cannot be affine on the whole real line.
Consequently both preactivation diagonal slopes vanish. The diagonal
slope of R is one.

Subtracting x3 reduces the equation to the nine-dimensional invariant
feature space used in the checker: six oriented comparison ReLUs and
three independent linear differences. On each braid cone the sum of
the two convex folds is linear; each fold is therefore individually
linear. Its preactivation has constant weak sign on each cone.

A preactivation with globally one weak sign contributes a shallow
function and needs no mixed fan. Otherwise its cut-ray signs occur in
the exhaustive comparability-graph enumeration.

## Quotient coordinates

The checker verifies exactly that M has rank nine, P has rank five,
and P*M=0. Thus P gives the full quotient of fourteen cut values by
the shallow invariant feature space.

I additionally checked directly, with rational arithmetic, that P sends
the cut values of the following five functions to the five standard
basis vectors, in the order shown:

    max(x0,x1,x2)-x3,
    max(x0,x1,x3)-x3,
    max(x0,x2,x3)-x3,
    max(x1,x2,x3)-x3,
    Max4-x3.

Therefore the interpretation as four triple-max coordinates and one
quadruple-max coordinate is correct. The target coordinate is
`(0,0,0,0,1)`.

## Why the weak-cone cover is valid

All 6,437 mixed sign candidates modulo sign are examined. A candidate
either extends into one of the 57 supplied weak cones or has an exact
strict-infeasibility certificate. Extending a sign fan may assign a
sign at a cut where the original preactivation is zero. This does not
change the evaluated fold there; the added weak inequality is satisfied
with equality.

Coverage up to reversing every sign is valid because

    ReLU(-g) = ReLU(g)-g.

The two folds therefore have identical quotient coordinates. Replacing
a preactivation by its negative can be compensated within R.

The 57 cones need not be accepted on the basis of a numerical producer:
their required coverage is independently checked against the entire
candidate enumeration, and all exclusions are independently verified
with rational arithmetic.

## Certificate checks and theorem assembly

I reran the default exact checker successfully. It verifies:

* 6,023 covered candidates and 414 strict-fan exclusions;
* three canonical one-dimensional cones and 54 remaining cones;
* 108 single-cone exclusions, covering both signs of the target ray;
* 1,485 pair exclusions, covering every unordered pair with repetition
  among the 54 remaining cones.

For a weak system `C*z=b`, `A*z>=0`, the certificate checks
`y>=0`, `y*A=lambda*C`, and `lambda*b<0`. Any solution would give
`0<=y*A*z=lambda*b<0`. Strict-fan certificates instead use a nonzero
nonnegative y and a homogeneous equality, contradicting strict signs.
Both implications are valid exactly as implemented.

Each canonical cone contributes a nonnegative multiple c of the Max4
quotient. Consider an equation with at most two effective folds:

1. Both folds in remaining cones are impossible by the pair certificates.
2. If one fold is canonical with quotient c times the target, the other
   has quotient `(1-c)` times the target. The single-cone certificates
   exclude either nonzero sign of that multiple in every remaining cone.
   Thus such a remaining fold has zero quotient and is shallow.
3. If both folds are canonical, their nonnegative coefficients sum to one.

A globally one-signed fold has zero quotient and is handled by the same
single-effective-fold reasoning. No boundary cone is discarded.

## A stronger consequence visible in the checked data

The checker establishes more than the quotient statement for each
effective fold. A canonical cone has a one-dimensional coefficient
nullspace, and the checker verifies that its spanning preactivation
is proportional on all cut rays to an actual complementary-pair-max
difference. Since both preactivations are braid-linear and M has rank
nine, this is an equality of functions everywhere.

Hence every effective preactivation itself is a nonzero scalar multiple
of a complementary-pair-max difference, with either orientation. With
one effective fold its scalar has absolute value one. With two effective
folds the two absolute values sum to one. The folds can use different
pair matchings.

This stronger statement still concerns the enlarged comparison-feature
space. It does not assert that the affine residual can be reconstructed
with any specified number of actual second-hidden-layer neurons, and
does not by itself prove a component count for a network architecture.
