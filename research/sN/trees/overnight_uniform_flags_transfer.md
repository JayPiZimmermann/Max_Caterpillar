# A filtration-safe flag transfer and its outward-leaf obstruction

This is an exact obstruction to a **fixed block and single-anchor**
transfer. It does not exclude pairing-indexed sums retaining different
external normal or attachment states.

## The operator has the required filtration drop

Let \(h\) be a retained label and \(y_1,\ldots,y_k\) new labels.
Take a complete sequence of \(k\) independent directions on these labels,
extending each direction to have the same value at every retained label
as at \(h\). Apply the \(k\) successive opposite exposed-face differences.
Then identify every deleted input coordinate \(y_i\) with \(x_h\).
Call this linear operator \(R_{\mathcal U}\).

Each opposite-face difference lowers the support-function dimension
filtration by one, or is zero. Restriction preserves the filtration.
Consequently \(R_{\mathcal U}\) maps \(L_d\) into \(L_{d-k}\), in the range
where these indices are nonnegative. Thus this transfer avoids the
filtration failure of the preceding scalar curvature construction.

## Exact transfer on a grafted family

Let \(G(z)\) be the support function of a core zonotope \(Z\), and put
\(V(z)=\sigma(G(z))\). Attach the \(k\) new outward leaves at \(h\):

\[
 U(y,z)=\sigma\left(G(z)+\sum_{i=1}^k\sigma(y_i-x_h)\right).
\]

There is a number \(\eta_{\mathcal U}\), depending only on the complete
block flag, such that the following **whole-function identities** hold:

\[
\begin{aligned}
 R_{\mathcal U}U
    &=\eta_{\mathcal U}(V-G),\\
 R_{\mathcal U}\max_{\{y_i\}\cup\mathrm{retained}}
    &=\eta_{\mathcal U}(\max_{\mathrm{retained}}-x_h).
\end{aligned}
\]

To prove this, project the support polytopes to their coefficients on the
new coordinates. The grafted pyramid projects to the cube \([0,1]^k\),
whereas the maximum simplex projects to
\(\operatorname{conv}(0,e_1,\ldots,e_k)\).
Both have the identical negative orthant as their normal cone at zero.
Each signed branch of a complete flag selects a unique projected vertex,
equivalently by a sufficiently small lexicographic perturbation of its
directions. Hence the coefficient of the zero fiber is the same for the
two polytopes; call it \(\eta_{\mathcal U}\).

For the grafted pyramid, the zero fiber is \(\operatorname{conv}(0,Z)\).
Every other cube vertex has a translated copy of \(Z\) as its fiber.
Identifying \(y_i=x_h\) removes those translations.
For the maximum, the zero fiber is the retained simplex and all other
fibers become the single point at \(h\).
Finally, the sum of coefficients of all signed branches is
\((1-1)^k=0\). This proves the two displayed identities.

The first identity can also be written
\(R_{\mathcal U}U=\eta_{\mathcal U}\sigma(-G)\).
Modulo the shallow span this is the same core class as \(V\).

## Why it prevents matching consumption

Take a five-label canonical core unit whose nonapex tree has four vertices,
and attach four new leaves to a nonapex vertex \(h\).
The resulting eight-vertex tree has matching number at most two:
after removing \(h\), the old tree has only three vertices and all new
vertices are isolated. At most one matching edge meets \(h\).
In particular the grafted tree has no perfect matching.

If a core separator detects any such core unit, the transferred separator
detects its matching-deficient graft whenever
\(\eta_{\mathcal U}\ne0\). Conversely, if a fixed-block transfer followed
by a scalar core functional annihilates every such graft, then it
annihilates every core unit. Since the known core dictionary spans its
maximum modulo lower-dimensional terms, it must also annihilate the
transferred maximum.

The argument allows linear combinations of complete block flags and
different scalar core functionals, provided the block and single anchor
remain fixed. Their coefficients simply combine into a core functional.

## Six-flag positive control

overnight_uniform_flags_transfer.py uses the existing six five-label
flags, adds their final coordinate direction as the fourth exposed-face
difference, and chooses the fifth local label as the retained anchor.
It verifies the two virtual-polytope identities directly from complete
vertex lists. The core is the inward path with edges
\((2,1),(3,2),(4,3)\); the new leaves attach at label \(1\).
It also checks the matching number by enumerating all edge subsets.

The original complete-flag separator is then evaluated directly on the
core pyramid, core zonotope, and simplex. Thus the control uses the
known nonzero target and independently verifies the bad-tree obstruction,
without Fourier kernels or a rank computation.
The exact values are in overnight_uniform_flags_transfer.json.

The remaining structural requirement is explicit: a viable uniform
recurrence cannot collapse all retained direction values to one anchor.
It must retain distinguishable external normal/attachment states, or use
a pairing-indexed assembly with a proved cancellation across such states.
