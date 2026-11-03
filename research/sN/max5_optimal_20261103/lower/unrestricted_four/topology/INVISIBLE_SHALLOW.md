# Triple-contact data do not determine a shallow core

Status: elementary mathematical proof, 3 November 2026. This is a barrier
to a proposed lower-bound shortcut, not a construction of a width-four
MAX5 network. No Lean verification is claimed in this note.

## Exact example

Write `sigma(t)=max(t,0)`. Partition the input labels as

```
P={0,3,4},     Q={1,2},
u=x0+x3+x4-2*x1-2*x2.
```

The finite shallow function

```
K(x) = sigma(u+x0)+sigma(u+x3)+sigma(u+x4)
       -2*sigma(u+x1)-2*sigma(u+x2)
```

has all of the following properties.

1. It uses five homogeneous first-layer ReLUs. Every first normal has
   coordinate sum zero and full support.
2. It is invariant under common translation and is even.
3. It vanishes at every input at which at least three coordinates attain
   the maximum. This includes every whole triple-contact segment and cone,
   not just finitely many test points.
4. It vanishes on an open neighborhood of each four-way contact
   `q_i=-e_i`. Thus adding it to any core preserves every directional germ
   at those five contacts, as well as all their higher local information.
5. It is nonzero: `K(0,0,2,1,2)=-1`.

The five literal normals, in the displayed term order, are

```
(2,-2,-2,1,1),
(1,-2,-2,2,1),
(1,-2,-2,1,2),
(1,-1,-2,1,1),
(1,-2,-1,1,1).
```

The first three output coefficients are `1`, and the last two are `-2`.
The exact independent finite arithmetic controls are in `verify.py` and
`verification.json`. The proof below covers every real input in the stated
sets; it does not infer this from a numerical sample.

## Proof

Let `c_i=1` for `i in P` and `c_i=-2` for `i in Q`. Then
`sum c_i=-1`, `u=sum c_i*x_i`, and

```
K(x)=sum_i c_i*sigma(u+x_i).
```

Each `u+x_i` is invariant under common translation: translating every
coordinate by `t` changes `u` by `-t`. The identity
`sigma(z)-sigma(-z)=z` gives

```
K(x)-K(-x)
  = sum_i c_i*(u+x_i)
  = -u+u=0.
```

For the contact claim it is enough, by translation invariance, to take
`x=-s*e_i-t*e_j`, where `s,t>=0` and `i,j` are distinct. These inputs cover
all points with at least three maximizing coordinates after subtracting
the common maximum. A single negative coordinate is included by setting
one scalar to zero, and the diagonal case has both scalars zero.

If both `i,j` belong to P, then `u=-s-t` and every `u+x_k` is nonpositive,
so every ReLU is zero. If both belong to Q, then `u=2(s+t)` and every
`u+x_k` is nonnegative; hence the preceding linear identity gives `K=0`.

In the remaining case arrange `i in P`, `j in Q`. Then `u=-s+2t`.
The three other labels have total coefficient `2-2=0`, so their common
term `sigma(u)` cancels. The two remaining terms are

```
K(x)=sigma(2(t-s))-2*sigma(t-s)=0.
```

At `q_i` with `i in P`, the five preactivations are `-2` at label i and
`-1` elsewhere. They remain negative throughout an open neighborhood,
where K is identically zero. At `q_i` with `i in Q`, they are `1` at label
i and `2` elsewhere. They remain positive throughout an open neighborhood,
where their weighted linear sum is identically zero.

Finally at `(0,0,2,1,2)`, the value of u is `-1`. The three P terms sum to
`1` and the two Q terms, with their coefficients, sum to `-2`. Thus K=-1.

## Consequence for the lower-bound search

For any finite shallow core g, the family `g+lambda*K` has the same odd
linear form, the same values on the entire triple-contact locus, and the
same full local germs at all five four-way contacts, for every real lambda.
These are invariant homogeneous shallow functions whenever g is one.
One may adjoin the five displayed features to a common dictionary.

Consequently, zero-set coverage of the triple-contact locus, the five
local MAX4 reductions, and the odd-core constraints cannot by themselves
reconstruct a general core or force its nonroot first normals to disappear.
This observation does **not** show that those necessary conditions are
jointly consistent with an exact two-core MAX5 identity. The full identity,
including curvature cancellation away from the triple-contact locus,
can still exclude every such candidate.

In particular, the example does not refute the segment obstruction with
a restricted dictionary: adjoining five full-support features changes
the first-width budget and creates many additional crossing rows. It
explains precisely why the unrestricted-first-width problem needs a
global cancellation argument in addition to the successful local tests.

## General family behind the example

The same mechanism works for a partition with sizes p>q>=2. Set

```
alpha=(q-1)/(p-q)>0,
beta=-(p-1)/(p-q)<0,
c_i=alpha on P and beta on Q,
u=sum_i c_i*x_i,
K=sum_i c_i*sigma(u+x_i).
```

Then `alpha+beta=-1` and `sum_i c_i=-1`. Translation invariance,
evenness, and vanishing near every `-e_i` follow exactly as above. On a
mixed two-coordinate negative cone the outside coefficients sum to zero,
while the two remaining terms are

```
alpha*sigma(beta*(s-t))+beta*sigma(-alpha*(s-t))=0.
```

On same-part negative cones all preactivations have one sign. Thus K
vanishes wherever at least p+q-2 coordinates share the maximum. The
smallest nontrivial instance of this family is p=3,q=2, namely MAX5.
