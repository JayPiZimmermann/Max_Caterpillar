# A simple obstruction to the tropical-min composition route

This excludes one proposed reduction, not a general two-hidden-layer
construction. No Lean theorem is claimed.

Put

\[
L_i(x)=x_i+\sum_j\sigma(x_j-x_i).
\]

Then `min_i L_i(x)=max_i x_i`. Indeed, if
`x_1 >= ... >= x_N`, the first two values of `L` equal `x_1`, and

\[
L_{k+1}-L_k=(k-1)(x_k-x_{k+1})\qquad(k\ge2).
\]

Consequently the image of `L` is exactly the set `D` where the minimum
coordinate is attained at least twice: the displayed equations recover
the successive gaps of `x` from any ordered point of `D`.

One tempting route was to extend `min|D` by a one-hidden-layer ReLU
function of the `L_i`. A fixed finite alphabet of coefficients would then
give an exponential two-hidden-layer dictionary using the functions
`sigma(x_i-x_j)` in its first hidden layer.

**This is impossible for every `N>=5`, even with arbitrary coefficients.**
For every homogeneous one-hidden-layer ReLU function `F`, the function
`F(y)-F(-y)` is linear, by `sigma(t)-sigma(-t)=t`. If an extension exists,
average it over coordinate permutations. Its odd difference is now
`alpha sum_i y_i`. Agreement on constant vectors gives `alpha=2/N`.
But for

\[
y=(0,\ldots,0,1,1)
\]

both `y` and `-y` belong to `D`. Hence the required difference is
`min(y)-min(-y)=1`, whereas the forced linear difference is `4/N`.
These disagree for `N>=5`. Biases do not help: taking recession functions
preserves agreement with the homogeneous target on the cone `D`.

The finite histogram tests in `overnight_upper_tropical_min.py` preceded
this argument. For the alphabets `[-2,2]` and `[-3,3]`, the exact rational
constraint ranks at `N=5` were respectively `6/7` and `16/17`.
The elementary proof supersedes those finite exclusions and explains why
widening the coefficient alphabet cannot repair this route.

The obstruction concerns only factoring through this particular map `L`
and then applying one hidden layer. It does not exclude a general signed
combination of second-hidden-layer units using the original pair
comparisons, full-label circuit bases, or noncrossing trees.
