# Further exact failures beyond canonical trees

25 October 2026. These tests address broader network models. None is an
unrestricted impossibility theorem, and none proves an exponential upper
construction. Every exclusion below has an exact rational evaluation rank
lower bound and, when needed, independent exact rational-function null vectors.

## Midpoint-centre stars

For distinct labels `a,c,d`, put `m=(x_c+x_d)/2` and use

\[
\sigma\!\left(m-x_a+\delta(x_c-x_d)+
 \sum_{i\ne a,c,d}h_i(x_i-m)+\frac{|x_c-x_d|}{2}+
 \sum_{i\ne a,c,d}\sigma(x_i-m)\right).
\]

The features comparing an input with a midpoint are outside the paper's
pair-comparison tree model. The first hidden layer has polynomial size and
fixed finite head sets give exponentially many units and face descriptions.
For `delta in {0,1/2,1}`, the integer leaf set `{-2,-1,0,1}` fails already
at four inputs, with 12 columns and augmented rank 13. Adding leaf value
`-1/2` gives 15 columns and augmented rank 16. Both column families have full
ordinary rank, so no nullspace gate is needed for those finite exclusions.

Their unions with ordinary general-head stars were also tested, because two
separate failures do not imply that the union fails. At five inputs the
integer union has 50 columns, ranks 48/49, and two exact null vectors. The
union with the additional half head has 80 columns, ranks 74/75, and six exact
null vectors. Coordinate deletion preserves the union modulo lower terms:
deleting an outer leaf survives only for head 0 or -1, and deleting either
midpoint coordinate freezes every generator. These union exclusions therefore
hold for every arity at least five. The single-circuit tests subsequently
enlarge these midpoint cores to all possible core sizes.

## Unequal effective generator lengths

Permit an apex coefficient `-c` with `c in {1,2}`, leaf heads
`h_i in {-3,-2,-1,0,1,2}`, and centre coefficient `c-sum_i h_i`. The generators
are the ordinary star differences. Dividing the preactivation by `c` gives
a canonical apex with generator lengths `1/c`, so this is a genuine weighted
reopening of the earlier unit-length star model. Its generic Fourier function is

\[
\frac{c^{N-1}(-\omega_a)^{N-4}}
 {\prod_{i\ne a,b}(c\omega_i+\omega_a h_i)
                       (c\omega_i+\omega_a(h_i+1))}.
\]

At five inputs, all 112 histogram columns have ranks 94/95; all 18 independent
null vectors pass the exact principal-parts gate. One entire row is checked
by inverting every atom's coordinate matrix, whose determinant has absolute
value `c`. The receipt is `overnight_upper_weighted_star_5.json`.

Deleting a leaf again leaves a smaller same-family unit only for head 0 or
-1, and preserves `c`; other cases are first-hidden-layer functions. Thus
this failure propagates to every `N>=5`.

This also rules out the corresponding full-dimensional box-pyramid stars
whose inner star uses all labels and whose head coefficients lie in
`{-3,...,2}`. In the independent-generator basis, the base is the box
`product_i[h_i,h_i+1]`. The convex hull of the origin and that box is tiled
by the box and the pyramids over its visible facets. The box itself has a
first-hidden-layer support function. Visible facet coordinates are `±1` or
`±2`; deleting that generator gives one of the weighted omitted-apex stars.
For positive facet coordinates, reflect the resulting atom. Reflection
multiplies its generic rational Fourier function by `(-1)^N`, so reflected
atoms do not enlarge the tested Fourier span. The remaining heads transform
by `h -> -h-1`, which preserves this set. Larger head magnitudes can introduce
new generator lengths and are not covered.

## Two positive circuits joined by a mean comparison

Choose disjoint nonempty nonapex cores `S,T`, with means `mu_S,mu_T`.
Use the bridge generator `mu_S-mu_T`, core generators `x_i-mu_S` on `S`,
core generators `x_i-mu_T` on `T`, and outside-leaf generators `x_i-mu_T`.
The head is `mu_T-x_a` plus `delta` times the bridge and a linear combination
of all other generators. The tested coefficients are `delta in {-1,0,1}`,
outside heads `{-1,0,1}`, and normalized core heads `{0,1,2}` with minimum zero
on each core. Add every generator through its positive part.

Each core has one positive dependence. Product tiling omits one generator
`j in S` and one `k in T`. The atom coordinates have inverse Jacobian
`|S||T|`; the bridge Fourier factor is

\[
\bigl(\sum_{i\in S}\omega_i+\omega_a\delta\bigr)
\bigl(\sum_{i\in S}\omega_i+\omega_a(\delta+1)\bigr).
\]

Other factors are the audited single-core factors within each core and the
ordinary leaf factors outside. The parent independently derived this product
tiling and Jacobian. The checker also verifies an entire row by exact atom
coordinate inversion.

The raw two-core family has 135 histogram columns at five inputs, ranks
83/84, and 52 exact null vectors. Deleting a singleton core can leave a full
single-core circuit, so those terms must be included before claiming deletion
closure. The complete union adds ten full-single-core columns. Its 145 columns
have ranks **93/94**, with the same 52 exact null vectors; see
`overnight_upper_two_circuits_union_5.json`.

The union is closed under the relevant top-class coordinate deletion. Outside
leaf deletions retain the same family for heads 0 or -1. A core deletion with
at least two labels freezes that core and the bridge, leaving too few free
generators to contribute in the next top quotient. Singleton exceptions give
the adjoined single-core units; single cores with outside leaves were already
included by taking a singleton first core. Thus the exact union obstruction
propagates to all `N>=5`.

This was still a genuinely exponential candidate: three choices of label
role and three head choices give at most `poly(N)9^N` full descriptions;
three face states per generator give at most `poly(N)27^N` descriptions.
Mean-to-mean comparisons on disjoint subsets require at most `poly(N)3^N`
first-hidden-layer functions. The failure concerns the specified head sets
and bridge parameters, not all two-circuit constructions.

Reproduction uses the corresponding `overnight_upper_midpoint.py`,
`overnight_upper_joint_stars.py`, `overnight_upper_weighted_star.py`,
`overnight_upper_two_circuits.py`, and
`overnight_upper_two_circuits_union.py` scripts. Runner logs and exit records
store the exact commands. All results remain research certificates rather
than Lean-verified declarations.
