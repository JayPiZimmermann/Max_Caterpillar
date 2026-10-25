# A shallow classifier for three simultaneous comparisons

This is an exact positive construction for a sign test, not a finite-width
representation of `max_5`. It prevents a proposed lower-bound argument
from assuming that the conjunction of three comparisons cannot be the
positive set of a shallow preactivation.

For `x=(x1,x2,x3)`, define the homogeneous shallow function

```
F(x)=2 sum_(i<j) (|xi+xj|-|xi-xj|)
       -3|x1+x2+x3|
       +|x1+x2-x3|+|x1-x2+x3|+|-x1+x2+x3|,
g(x)=x1+x2+x3-|x1|-|x2|-|x3|+F(x)/4.
```

Then `g(x)>0` exactly when all three coordinates are strictly positive;
`g(x)=0` on the boundary of the nonnegative orthant; and `g(x)<0` if any
coordinate is negative. All coefficients are rational.

## Proof and exact identity

Put

```
T(u,v,w)=|w+u+v|-|w+u-v|-|w-u+v|+|w-u-v|.
```

Then

```
F(x)=sum_i [T(x_j,x_k,0)-T(x_j,x_k,x_i)],
```

where `{i,j,k}={1,2,3}`. The bracket is even in `x_i`, odd in each of
`x_j,x_k`, and nonnegative when all coordinates are nonnegative.
For positive sorted magnitudes `r1>=r2>=r3`, let
`tau=(r2+r3-r1)_+`. The three bracket magnitudes are

```
4r3-2tau, 2tau, 2tau.
```

Consequently, on the positive orthant,

```
F=4 min(x)+2(sum(x)-2 max(x))_+,
```

and on every orthant,

```
|F(x)| <= 6 min_i |xi|.
```

Each bracket vanishes if any coordinate is zero. Thus on the positive
orthant `g>=min(x)>0`. If a coordinate is negative, the linear-minus-
absolute-value term is `-2 sum_(xi<0)|xi|`; the bound on `F/4` makes the
sum strictly negative. The cases with zero coordinates follow directly.

Let

```
q(x)=max(0,min(x1,x2,x3)),
A(x)=(-x1+x2+x3, x1-x2+x3, x1+x2-x3).
```

There is the exact global functional equation

```
sigma(g(x)) = q(x) + (1/2) q(Ax).                    (1)
```

On the positive orthant, this is the displayed formula for `F`. Outside
it, the left side is zero, and `q(Ax)=0`: the inverse of `A` has zeros
on its diagonal and `1/2` off its diagonal, so `Ax>0` would imply `x>0`.

The standard-library checker
`overnight_fixed_classifier_control.py` independently verifies (1) on
all rays of the complete13-hyperplane arrangement. It also checks the
sign of `g` in every coordinate orthant. All expressions are linear on
each resulting cone, so the ray check proves the whole-domain identity.
The strict sign assertions use the analytic bounds above.

```
python3 overnight_fixed_classifier_control.py
```

## Why this does not give a finite-width solution

Rearranging (1) gives

```
q = sigma(g) - (1/2) q composed with A.
```

Iteration yields an alternating geometric expansion in single outer
ReLUs of shallow functions. The sum of coordinates is preserved by `A`,
while differences are multiplied by `-2`. Thus for a nondiagonal point,
`A^k x` eventually leaves the positive orthant, but the required number
of terms is not uniformly bounded near the diagonal. On the diagonal
it never leaves. The residual nevertheless tends to zero: whenever
`q(A^k x)>0`, it is bounded by `sum(x)/3`, and it is multiplied by
`2^-k`.

This is a convergent infinite expansion, not an exact finite network.
It gives a concrete reason that an excellent approximation or a small
residual does not establish a finite-width construction. It also shows
that values, not only activation signs, matter in the unrestricted
three-free-neuron problem.
