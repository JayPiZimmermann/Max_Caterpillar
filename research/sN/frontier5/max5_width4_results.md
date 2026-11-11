# Max5 second width four: new unrestricted restrictions

## Current outcome

This branch does not prove existence or nonexistence of an unrestricted
two-hidden-layer Max5 network with second hidden width four. The current
unrestricted second-width interval remains four through six. The following
new mathematical restrictions have independent audits; no new Lean
formalization is claimed.

## 1. Complete functional classification of one-core Max4

For arbitrary finite shallow R,g, including biases, an identity
`Max4=R+d*ReLU(g)` requires d>0. After absorbing d, the two shallow
branches R and R+g are complementary pair maxima. The positive branch
classification was already available; the new part excludes d<0 without
restricting first hyperplane directions.

The new proof uses the odd-kernel matching, an exact ReLU clipping
identity, and constant shallow ridge coefficients. It extends the
previous complete-comparison-dictionary Boolean obstruction.

* Proof: `max5_width4_negative_core.md`.
* Independent audit: `max5_width4_negative_core_audit.md`.

In a two-core Max5 identity with mixed output signs, the sole positive
core must therefore vanish at every four-way top tie. If both output
signs are negative, both cores vanish at every four-way top tie.
Whenever one core uniquely vanishes, its local homogeneous germ on the
four tied coordinates is a complementary-pair comparator.

## 2. Antipodal ties force actual gate zeros

For a general representation `Max_n=R+sum d_k*ReLU(g_k)` with continuous
functions having linear odd parts, let V be the common odd kernel. At a
nonconstant v in V let A and B be its maximum and minimum label sets,
and let Z contain the cores actually zero at v. Then

```
rank of the odd forms indexed by Z >= max(|A|,|B|)-1.
```

The proof compares projected coordinate simplices after restricting to
the kernels of the zero-gate odd forms. It does not assume shallow
preactivations beyond their linear odd parts.

For Max5's equality diamonds, this forces both cores to vanish on the
three-versus-two tie line at each open diamond edge. At the ordinary
two-versus-two corner lines, a sole zero core must have odd form
proportional to the pair-sum difference. If neither odd form has that
direction, both cores vanish on both corner lines.

* Proof: `max5_width4_antipodal_zero_gates.md`.
* Independent audit: `max5_width4_antipodal_zero_gates_audit.md`.

If one odd form is the complementary-pair sum difference, a further
normalization is available on the complete closed equality diamond:
after formally complementing the other gate, the shallow remainder's
odd part is a combination of those two pair sums, with coefficients
summing to one and no singleton-input coefficient. This uses an exact
clipping formula and two incompatible shallow ridge patches. It does
not exclude the normalized slice, which has explicit realizations.

* Proof: `max5_width4_antipodal_slice.md`.
* Independent audit: `max5_width4_antipodal_slice_audit.md`.

Simultaneous zero cores may cancel through intermediate hinges. For
example the local odd-response identity
`(ReLU(A)-ReLU(C))+(ReLU(C)-ReLU(B))=ReLU(A)-ReLU(B)`
allows independent odd directions A-C and C-B. Thus the zero theorem
alone does not force one actual core to use the pair-sum direction.

## 3. Shifted tails admit only subset-sum-compatible patterns

The one-pass-per-diagonal-end case has a nonnegative identity

```
L+sum s_i*(ReLU(w_i+delta_i)-ReLU(w_i)) >= 0.
```

On the common shift kernel, at any point where every w_i is nonzero,
its active set A must satisfy the exact covector equation

```
L+sum_{i in A} s_i*delta_i = 0.
```

For two nonzero proportional shifts whose ratio is not +1 or -1, the
four subset sums are distinct. A Max5 solution in this case requires
an open zero plateau of at least one free preactivation on the
four-dimensional shift kernel; otherwise both signs are fixed there
and the target restriction would be shallow, which is impossible.
An explicit exact example demonstrates why the plateau possibility
cannot be discarded from the general positivity argument.

* Proof: `max5_width4_shifted_subset.md`.
* Independent audit: `max5_width4_shifted_subset_audit.md`.

At first width nine, the (1,1,7) row-sum split has zero shifts, and
pure-root (2,2,5) C5 dictionaries have shift rank at most one. These
restrictions make the first-width-nine completion problem more structured,
but other invariant-support families remain separate.

## Remaining global obstruction

The unresolved mechanisms are simultaneous zero cores and their interior
cancellation in the two-core case, and resonant/dependent shifts or
open zero plateaus in the shifted-tail case. The equality-diamond
classification is necessary data, not a parameterization of actual
networks. The new conditions may be imposed on searches, but numerical
search failure on these constrained families is not an exclusion.

## 4. First-width-nine budget strengthens the contact bound

A core can uniquely carry at most three four-way contacts by root-ridge
combinatorics. Exactly three would force the triangle-plus-edge root
graph. Arbitrary nonroot features can supply the necessary local affine
corrections, so root curvature alone does not improve this to two.

However, in an actual network, three such contacts require at least
eight invariant first hyperplanes, hence first width at least ten.
Four roots and three nonroot corrections would exhaust a seven-row
invariant budget. The first-layer support cover then requires two
different external-coordinate columns, while the local gradient
equations force them into a common one-dimensional kernel, a
contradiction.

Therefore at first width nine each free core uniquely carries at most
two contacts. With two positive cores at least one contact is shared;
with mixed signs at least three are shared; with two negative cores
all five are shared. These constraints retain simultaneous-zero cases.

* Proof: `max5_width4_quad_budget.md`.
* Independent audit: `max5_width4_quad_budget_audit.md`.
* Independent local example audit: `max5_width4_quad_local_audit.md`.
