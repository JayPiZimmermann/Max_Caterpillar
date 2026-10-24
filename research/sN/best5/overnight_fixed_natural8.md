# Natural eight-row first hidden layer: current search

**Research only. The natural eight-row layer requires second width at
least seven, by an independently checked exact finite certificate and
the written translation reduction. No construction at first width eight
has been found.** A five-free-neuron identity, which would give second
width seven, is the current constructive target. This result is not
Lean verified.

Use coordinates `(x0,x1,x2,x3,x4)=(reference,u,v,s,t)` after subtracting
the reference coordinate. The invariant first-layer span is

```
W6 = span{sigma(u), sigma(v), sigma(u-v),
          sigma(s), sigma(t), sigma(s-t)}.
```

The complete first hidden layer adds `sigma(x0),sigma(-x0)`. The same
two-translation proof as in `overnight_fixed_bowtie.md` gives
`h2*=k_W6+2`, with the convention that both sides are infinite if no
finite representation exists. The independent first-layer classification
in `../frontierN/overnight_general_six.md` identifies every possible
eight-row first layer with this one up to scaling and relabeling.

## Complete real-parameter K4 search

There are 147 vanishing flats, including zero; 146 nonzero flats give
81 potential-contribution masks. No triple of masks covers all required
localities. There are 3,418 unordered covering quadruples, including
repetition, or 54,688 quadruple/sign cases. All have been excluded by
the cone relaxation of the 26 locality equations and 24 Boolean-ray
equations eliminating the six-dimensional remainder. No circuit cuts
or closed-sign branch search was needed in these exclusions.

The independent standard-library coverage program
`overnight_fixed_natural8_coverage.py` regenerated every flat and every
quadruple in 1.73 seconds. Its receipt is
`overnight_fixed_natural8_coverage.json`. The durable cone producer is
`overnight_fixed_natural8_certify.py`; the independent equation/Farkas
checker is `overnight_fixed_natural8_verify.py`.

The independent checker passed all 54,688 cases in 8.34 seconds. Every
case is a direct rational separation using only the unreduced fifty
equations and nonnegativity of absolute values. There are no circuit
inequalities or sign trees in this proof. The compressed artifact is
609 KiB; its SHA-256 is
`394b2f9f139f4b48ee47cfff1df8453c1ca8eeeb6117c7a6ce5d4eb308a56e88`.
The receipt is `overnight_fixed_natural8_check.json`.

At most three nonzero terms can be padded to four by splitting a term
into positive rescalings of itself. Repeated flats and independent
copies of their parameter blocks are explicitly allowed. The zero-term
case is excluded by the fifth mixed difference, which vanishes on W6
but is one on the target. Thus the independent K4 gate proves `k_W6>=5`
and `h2>=7` for this first hidden layer, without using the earlier K2
certificate. Combined with the independent first-layer classification,
this gives the unrestricted implication `h1=8 => h2>=7` at five inputs.
It does not assert that any network with first width eight exists.

Reproduce the independent gate from this directory:

```
python3 overnight_fixed_natural8_coverage.py
python3 overnight_fixed_natural8_verify.py
```

The producer uses the existing research environment:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  ../dfs/h4-general-neurons/venv/bin/python \
  overnight_fixed_natural8_certify.py --budget 1200
```

## Structured construction instrument

For each group, put `(a,b,p)=(sigma(u),sigma(v),sigma(u-v))`. Its image
consists of three cones:

```
a=b+p, b,p>=0;     p=0, 0<=a<=b;     b=0, 0<=a<=p.
```

The group maximum is `a+b-sigma(a-p)`. The product image has nine
four-dimensional cones. On each, the target is the maximum of two
linear forms. For a proposed dictionary of outer linear forms, group
all their interior kink hyperplanes by exact proportionality. Equating
the jump coefficients, including zero on unwanted hyperplanes, and
equating values on the Boolean rays is sufficient for a global identity.
This allows unwanted bends to cancel and is stronger than sample fitting.
The method passes the exact known `(10,6)` identity on its corresponding
sixteen product cones; see `overnight_fixed_dictionary_control.json`.

The following finite dictionaries gave nonzero numerical residuals:

| invariant feature span | coefficient box | primitive outer forms | maximum residual |
|---|---:|---:|---:|
| W6 | `[-2,2]^6` | 7,448 | 0.01433 |
| W6 | `[-3,3]^6` | 58,096 | 0.003903 |
| W6 | `[-4,4]^6` | 257,544 | 0.001718 |
| W6 plus `sigma(-t)` | `[-2,2]^7` | 37,969 | 0.003982 |
| W6 plus `sigma(-t)` | `[-3,3]^7` | 409,585 | 0.0008274 |

These are numerical diagnostics on the declared integer dictionaries,
not lower bounds for arbitrary real coefficients or arbitrary width.
Reopening condition: a different structured dictionary, a rational
candidate outside these boxes, or an analytic cancellation identity.

## Arbitrary-width obstruction attempted

The four group rays are

```
r0=(0,1,0), r1=(1,1,0), r2=(1,0,1), r3=(0,0,1),
r0-r1+r2-r3=0.
```

Their target group values are `(1,1,1,0)`, which do not satisfy this
linear relation. If an outer form has values `alpha_i` and `beta_j` on
the two groups' rays, both alternating sums vanish. On the quadrant
generated by one ray from each group, its kink occurs at the ratio
`-beta_j/alpha_i` when the signs differ. The target has a kink at ratio
one for `i,j<=2` and no kink if either index is three. A finite-measure
conservation or propagation argument using these relations remains open.

The current fifty locality/ray equations cannot supply an all-width
linear separator. On every flat, the distinct absolute linear forms
are linearly independent as functions of the flat parameters. Their
coefficient columns therefore span all possible one-neuron jet vectors.
Across all 146 flats there are 1,030 columns of rank 28, and the target
lies in their span. See `overnight_fixed_natural8_allwidth.json`.
Reopening condition: additional information that controls cancellation
of unwanted interior hyperplanes, beyond these fifty equations.

## Five-neuron pattern selection

A bounded mixed-integer relaxation selects at most five flat/sign
groups, with independent nonnegative absolute-value variables. It is
only a heuristic pattern selector: its magnitude cap and convexification
prevent negative conclusions about the original real-parameter problem.

The first selected pattern was

```
(12153,+), (14645,-), (15935,-), (26865,+), (27635,+).
```

The shared-parameter search found no exact rational witness on its
assigned exact strata (4,867 nodes, 40.5 seconds). This is recorded as
`NO_RATIONAL_WITNESS`, not as an independently certified exclusion.
The next selector adds valid short-circuit inequalities and excludes
previously tried patterns. Any actual candidate must pass exact global
cone verification before it is called a construction.
