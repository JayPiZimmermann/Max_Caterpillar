# Exact involutive folding and the natural odd-cycle obstruction

**Results:** an exact shallow folding of two reflected three-variable
positive minima, and a uniform denominator proof that the natural
coordinate-conjugate reflections have no odd folding cycle for every
`N>=4`. These are statements about a proposed construction mechanism.
They neither prove an unrestricted network-width lower bound nor exclude
other transformations or additional functional linear identities.

## A finite-order folding identity

Let

```
q(x)=max(0,min(x1,x2,x3)),
S=(2/3)J-I,
T=(2/3)(x1+x2+x3),
range(x)=max(x)-min(x)=1/2 sum_(i<j)|xi-xj|.
```

The map `S` is an involution. Define the shallow function

```
g(x)=T-range(x)
       + sum_i sigma(-xi) + sum_i sigma(-(Sx)i)
       - sum_(i<j) sigma(-xi-xj)
       - sum_(i<j) sigma(-(Sx)i-(Sx)j).
```

Then

```
sigma(g(x))=q(x)+q(Sx).                              (1)
```

To verify this, sort `x` as `u>=v>=w`. Before the two pair-sum
subtractions, the displayed function equals

```
q(x)+q(Sx)
 + sigma(-u)+sigma(-v)+sigma(v-T)+sigma(w-T).
```

For any vector `z` with three coordinates, the sum of the negative parts
of its two largest coordinates is at most
`sum_(i<j) sigma(-zi-zj)`. This is immediate by separating the cases of
zero, one, two, or three negative coordinates.

On the union of the positive orthant and its image under `S`, every
pair sum of both `x` and `Sx` is nonnegative. Indeed, if `y>0` then
`(Sy)i+(Sy)j=sum(y)/3+y_k>0`. Each vector has at most one negative
coordinate, so the excess terms and pair-sum subtractions both vanish.
The result is `q+qS`. Outside that union, both target terms vanish and
the pair-sum subtractions dominate the excess, leaving `g<=0`.
Continuity covers the boundaries and proves (1).

The standard-library checker `overnight_fixed_reflection_control.py`
verifies (1) globally on the92 rays of the complete15-hyperplane
arrangement and checks `S^2=I`. These walls include all coordinate and
transformed-coordinate boundaries, so each arrangement cone lies either
inside or outside the union of the two positive orthants. The checked
ray signs make `sigma(g)` linear on each cone. This is a finite exact
certificate, not a sampled test or a Lean proof.

The coefficient in (1) is necessarily one for a direct positive fold
`q+c qS=sigma(h)` with shallow `h` and `c>=0`. Along `x1=x2=z>0`, choose
first `z<x3<4z`: only the minimum of `x` contributes a normal jump, of
size `-1`. Next choose `0<x3<z`: only the minimum of `Sx` contributes,
of size `-c`. The target is positive near both pieces of the wall,
forcing `h` to equal it there. A shallow function has a single constant
jump coefficient on a fixed hyperplane, so `c=1`.

Thus (1) and its transform under `S` are the same equation. The
involution does not isolate `q`: its coefficient matrix is singular.
A possible alternative would be an odd cycle of distinct foldings.

## Natural coordinate-conjugate reflections

The three-variable function `q` corresponds to four full input labels:
for reference label `i`,

```
q_i(x)=max(0,min_(j!=i)(x_j-x_i)).
```

For general `N>=4`, let `n=N-1`, and define the natural reflection `R_i`
on `R^N` by

```
(R_i x)_i=x_i,
(R_i x)_j=(2/n) sum_(k!=i) x_k-x_j,   j!=i.          (2)
```

It fixes the reference coordinate and reflects the other coordinates
about their mean. Every `R_i` is an involution, fixes the common-shift
direction, and preserves the total coordinate sum. Coordinate
permutations conjugate these `N` reflections into one another. For
`N=4`, they are exactly the coordinate conjugates of the involution in
(1), after passing to difference coordinates.

## Uniform denominator proof

Set

```
e=gcd(n,2), d=n/e, c=2/e,
```

so `d>1`. Choose any prime `p` dividing `d`. The integer matrix `dR_i`
reduces modulo `p` to

```
dR_i = c u_i u_i^T   modulo p,                      (3)
```

where `u_i` has zero at coordinate `i` and one everywhere else. The
scalar `c` is nonzero modulo `p`: it is one when `n` is even, and it is
two with `p` odd when `n` is odd. The fixed-coordinate diagonal and the
identity part of the other block vanish modulo `p`.

For distinct indices,

```
u_i dot u_j = n-1 = -1 modulo p.
```

Consequently every nonempty reduced word, meaning adjacent indices are
distinct, satisfies

```
d^m R_(i1)...R_(im)
 = c^m (-1)^(m-1) u_(i1) u_(im)^T != 0 modulo p.   (4)
```

This follows immediately by multiplying the rank-one matrices in (3).
The outer product is nonzero. But if the product were an integer matrix,
its multiplication by `d^m` would be zero modulo `p`. In particular,
no nonempty reduced word can be the identity or an integer permutation
matrix.

Thus the reflections generate the free product of `N` copies of the
order-two group. After adjoining coordinate permutations, every word
has a unique reduced reflection word followed by a permutation: move
permutations to the right using conjugacy, and use (4) to rule out any
further relation. Reduced-word parity is therefore well-defined;
reflections have odd parity and coordinate permutations have even
parity. This proves the all-`N` statement symbolically. The small even,
odd, and composite-denominator matrix controls in the checker are only
sanity checks of (2)--(3), not evidence substituted for the induction.

## Function identifications do not create an odd cycle

In difference coordinates, the positive set of `q_i` is the positive
orthant. An invertible linear map preserving `q_i` must preserve that
cone, hence is a positive monomial map. Equality of the minimum for
all positive inputs forces every monomial scale to be one. Its linear
stabilizer is therefore exactly the coordinate permutations of the
other `N-1` inputs.

All maps in the group above fix the common-shift direction and preserve
the total coordinate sum. If two such maps agree with a permutation on
the quotient, their difference has the form `1 ell^T`; preservation of
total sum gives `N ell=0`, so they agree as full matrices. Equation (4)
therefore excludes a nonempty reduced reflection word from the
functional stabilizer as well.

It follows that the orbit of `q_i` has a well-defined parity. Any available or prospective folding that connects a function to its
image under one of these conjugate reflections changes that parity. The
resulting folding graph is
bipartite and has no odd cycle, even after identifying functions through
coordinate relabeling. Hence the proposed odd-cycle inversion cannot
arise from these natural reflections for any `N>=4`.

This conclusion does not exclude additional linear relations among
orbit functions, foldings with other coefficients or transforms, or
constructions outside this reflection family. In particular, it is not
an all-tree lower bound or a general finite-width impossibility result.

## Reproduction

```
python3 overnight_fixed_reflection_control.py
```

The earlier expanding-cone identity and its convergent but nonuniformly
terminating series are recorded separately in
`overnight_fixed_shallow_classifier.md`. The finite-order fold here
avoids that infinite-orbit issue only to encounter the singular
coefficient and the uniform no-odd-cycle obstruction above.
