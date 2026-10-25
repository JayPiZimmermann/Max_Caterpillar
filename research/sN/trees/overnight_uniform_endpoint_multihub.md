# Endpoint interpolation with several attachment vertices

This is an exact marked formula, not a separator theorem. Internal inward-cut
elimination preserving a deficient-tree ideal remains unproved; even after
such elimination, a global endpoint presentation is still needed.

Fix an all-positive rooted core C, reference root r, and its canonical kernel
F(a;omega). Root frequency is eliminated using total sum zero. Let T_h(b)
translate nonroot frequency h by b and rebalance the root; set T_r(b)=Id.
These translations commute. Attach k inward leaves, with m_h leaves attached
at core vertex h and sum_h m_h=k. Write formal variables u_h and
E(z)=sum_h u_h T_h(z).

Let a_0,...,a_k be the frequencies assigned to the apex and the k added leaves.
Sum over every choice of the actual apex and every assignment of the remaining
frequencies to the specified leaf slots. The exact result is

    (product_h m_h!)/(product_i a_i) [u^m]
    sum_i a_i^(k+1)/product_(j != i)(a_i-a_j)
          (product_(j != i) E(a_j)) F(a_i).

This finite omitted-factor formula requires no inverse of an operator. For a
fixed apex a_i, each new leaf gives (-a_i)/[a_j(a_j-a_i)] and shifts its hub by
a_j. Multiplying these factors gives precisely the displayed coefficient;
coefficient extraction assigns the leaves to hubs, and product m_h! accounts
for their distinguished slots. When a_i=a_j, the paired summands have equal
numerators and opposite simple residues, so the apparent singleton-diagonal
poles cancel. Equal-frequency values are obtained by rational continuation.
For a single hub the expression reduces to the ordinary divided difference
of z^(k+1)F(z;hub+sum_i a_i-z), divided by product_i a_i.

The endpoint tree has a perfect matching exactly when every m_h≤1 and the
core after removing occupied attachment vertices has a perfect matching.
This combinatorial criterion by itself does not descend to the rational
quotient. In particular the raw monomer-dimer polynomial cannot be the desired
functional: the already exact five-label relation equates the full orbit of
root1; edges(2,1),(3,2),(4,2) to three times the orbit of
root1; edges(2,1),(1,3),(2,4). The former is a nonmatching outward star; the
latter has two inward singleton leaves on a positive two-vertex core and has
a perfect matching. See `overnight_uniform_pruning_signed_relation.*`.
A valid matching separator is allowed to vanish on some matching trees.
