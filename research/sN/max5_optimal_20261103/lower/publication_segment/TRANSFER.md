# Local contact constraints for exact Max5 networks

The useful general lower-bound idea here is to inspect the network near a
tie of three maximum coordinates. A shallow ReLU function has a locally
linear odd part; the maximum at such a tie does not. Consequently, if

    MAX5 = R + ReLU(g) + ReLU(h)

and R,g,h are affine shallow functions, then at least one core vanishes at
every point `-a*e_i-b*e_j`, for `i != j` and `a,b > 0`. This statement,
including arbitrary biases and independent feature dictionaries, was
already verified in `triple_contact/TripleContact.lean`.

The new segment theorem concerns the actual common first-row array A and
signed coefficient vectors c,d, with

    g(x) = sum_j c_j*ReLU(A_j.x),
    h(x) = sum_j d_j*ReLU(A_j.x).

Both cores vanish at `-e3` and `-e4`. Apart from a distinguished physical
row k, every row omits coordinate3 or4, or satisfies `A_j3+A_j4=0`.
The total midpoint-hinge coefficient of these other rows is one in each
core; explicitly it is the signed sum of `c_j*|A_j3|`, respectively
`d_j*|A_j3|`, over balanced rows other than k. The exact Max5 identity
then forces

    A_k3 + A_k4 = 0.

This is `SegmentNetwork.exceptional_row_balanced`. Its proof directly
expands the finite first-feature sums on the segment joining `-e3` and
`-e4`, then applies the scalar piecewise-affine balance theorem. It retains
arbitrary real orientations, repeated rows, zero coefficients, and signed
cancellation. A second theorem, `no_three_coordinate_exception`, shows
that a zero-sum exceptional row cannot have exact support034,134,or234.

The accompanying generalization replaces the two unit midpoint masses by
arbitrary signed nonzero masses. Its guarded form says that either mass
is zero or the exceptional row balances. The pair version proves this
for every pair of distinct contact labels by an explicit permutation.
A separate actual-array theorem excludes the case with no exceptional
row at all when both signed midpoint masses are nonzero.

These are conditional statements about explicit real arrays, not merely
about an abstract encoded model. They do not establish the full contact
classification or exclude every ordinary network of widths(9,4).

The endpoint consequence is also useful. If both cores vanish at `-e_i`,
one of their one-sided derivatives toward `-e_j` must vanish. For a
homogeneous shallow core with linear head L, that derivative is

    -L_j + sum_r c_r *
      (if A_ri < 0 then -A_rj
       else if A_ri > 0 then 0
       else ReLU(-A_rj)).

The proof uses an exact affine identity on a sufficiently short ray and
the already verified weighted-contact theorem. The endpoint declarations
also include the corresponding formula with arbitrary first biases.

The actual segment cores are homogeneous. Applying this argument to an
ordinary biased no-skip network uses the existing recession theorem, which
drops biases while preserving both physical widths. Derived shallow
remainders are proof identities, not added physical skip connections.

The accompanying receipts separate exact Lean statements and their
standard-axiom checks from support classification and external arithmetic
certificates. This checkpoint contains no numerical width improvement or
claim that the optimal Max5 widths are determined.
