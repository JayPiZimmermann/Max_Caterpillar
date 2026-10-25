# Independent audit of the endpoint Q2 relation

Verdict: the exact rational identity proof is mathematically sound.
This review inspected the residue, DFS, coordinate and constant producers
directly. The root agent separately rebuilt the first-residue dictionaries
and replayed the three DFS gates without memoization. No producer artifacts
were changed by this review.

The endpoint hypothesis means every negative rooted cut is a singleton.
Consequently the only possible poles are ordinary subset sums and coordinate
diagonals. Every pole is simple before restriction. Full permutation symmetry
kills the diagonal poles: swapping their two labels fixes the divisor
pointwise and reverses the residue normal. Subsets and complements give
the same divisor, leaving only subset sizes 2, 3, 4 and coordinates at arity 9.

The recursive symmetry reduction is valid. Each cell refinement groups
physical labels with equal coefficients in a representative of the new
normal. Its permutations fix that normal and every preceding normal,
not merely the corresponding divisors. Therefore the restricted residue
remains invariant. An orbit containing an absent displayed denominator
cannot contain an actual pole. The algorithm checks all other pole orbits,
refuses unresolved multiple poles above dimension 3, and uses an exact
common-denominator numerator in the lower-dimensional leaves. With all poles
removed, strict negative homogeneous degree forces zero. Scalar normalization
of each node does not affect these assertions.

The surviving coordinate-only function has the form
$c/\prod_{i=0}^{8}\omega_i$: multiplying by that product gives a polynomial
of homogeneous degree zero on $\sum_i\omega_i=0$.
At the four required deletion arities, the actual-apex residue vanishes.
A nonroot leaf with sign $\epsilon$ contributes $-\epsilon$ times the
smaller canonical kernel. If the root itself is a leaf, its residue exists
only when the positive endpoint of its edge is its neighbor; the residue
is minus the smaller kernel rooted at that neighbor. These rules follow
directly from the two edge denominator factors. Fixing a deleted physical
coordinate leaves exactly the full permutation sum on the remaining labels,
so no factorial factor is missing.

For an independent constant check, I applied these direct rules four times
without the producer's root-slide preprocessing or colored-tree isomorphism
key. Combining only identical labelled root/edge descriptions leaves
83, 93, 72, and 48 states. I then recomputed every cut by removing its edge
and tested the full exact rational $S_5$ sum at
$(-40,1,3,9,27)$. Its value is exactly zero; the run took 0.097 seconds.
This independently confirms $c=0$.
The standalone replay is `overnight_upper_endpoint_q2_check.py`, with
receipt `overnight_upper_endpoint_q2_check.json`. It additionally recomputes
the initial rooted cuts by edge removal and confirms the endpoint condition
and 14 distinct denominator hyperplanes for every unit. Its 5,760 final
rational summands again sum to zero in 0.109 seconds. The receipt binds both
input hashes and the checker source hash.

Together with the root agent's separate exact score calculation of $-448$,
the relation disproves the current Q2 score as a functional on the generic
Fourier quotient, already on endpoint units. It is not a whole-function
identity and does not disprove the desired matching or outward-twin
separation theorem. No unrestricted exponential lower bound follows.
