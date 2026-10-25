# Matching states and inward-leaf divided differences

25 October 2026. These are exact local identities and a bounded modular
control. The uniform matching-deficiency separator and unrestricted
exponential lower bound remain open.

## Matching signatures at a cut

Let C_v,D_h be disjoint rooted trees joined by the edge vh. Write P(F) for
the number of perfect matchings of a forest F. Then

    P(C join D) = P(C)P(D) + P(C-v)P(D-h).

The two terms distinguish whether the joining edge is absent or present.
A forest has at most one perfect matching, but the identity does not need
that fact. When the joined tree has even order, an even/even cut uses only
the first term and an odd/odd cut only the second. Thus failure of a
perfect matching is a finite matching-state condition across a cut and
is unaffected by orientation reversal.

If the original head r and the attachment h are different retained marks,
one must also track deletion of both marks. For instance, deleting r from
the joined tree introduces P(D-{r,h}) in the term that uses vh. A two-mark
interface therefore carries the four values P(D-A), A subset {r,h}.
This bookkeeping is exact; it is not a construction of a functional on
rational kernels. Descent through the complete circuit relations remains
necessary.

## The broader seven-label endpoint control

The no-perfect-matching inventory has258 full-symmetry canonical tree
columns at N7. The77 columns in which every inward edge cuts off a single
child leaf have observed function rank16. The whole inventory has rank112.
The nonsingleton shifted-minus residue ranks for sizes2,3,4,5 are24,34,14,41,
with cumulative ranks24,52,66,96. Adjoining all these residue rows to the
original function rows still gives rank112, so the observed residue kernel
has dimension112-96=16, exactly the endpoint dimension.

The run used prime1000003 and64 exact-residue evaluation rows per size;
it took0.86 seconds. This is a necessary finite-field control only. It
neither proves the rational endpoint reduction at N7 nor an all-arity
presentation theorem. Source and inventory hashes are in the receipt.

## An exact endpoint operation

Let F be a lower canonical kernel with fixed apex frequency a and a fixed
attachment hub h. Graft k inward leaves with frequencies b1,...,bk at h,
keeping the head in the old tree. Removing these leaves and shifting the
hub by their total reproduces every surviving rooted cut. Comparing the
numerator powers gives the exact kernel

    (-a)^k F(apex=a, hub=omega_h+sum_j b_j)
       / product_j [b_j(b_j-a)].

Now fix k+1 frequencies a0,...,ak for the apex and these leaf positions,
and sum over the k+1 choices of apex, counting each remaining assignment
only once since all leaves share the same hub. Put

    t=omega_h+sum_i a_i,
    f(z)=z^(k+1) F(apex=z, hub=t-z),
    [a0,...,ak]f = sum_i f(a_i)/product_(j!=i)(a_i-a_j).

The sum is exactly

    [a0,...,ak]f / product_i a_i.

Indeed, the i-th graft factor equals
a_i^(k+1)/[(product_j a_j) product_(j!=i)(a_i-a_j)].
This proves the formula and retains all normalization factors. The
identity is initially read at distinct generic frequencies and extends
rationally; confluent values use the usual derivative limits. If the
leaf positions are fully permuted, an additional factor k! is present.

This divided difference removes the apparent singleton-minus diagonals
without assigning a score to a tree presentation. It is an actual linear
operation with fixed attachment data. With different hubs, the shifts
depend on the assignment and cannot be collapsed to this one-variable
formula. Nor does the formula map a lower maximum to the higher maximum.
Thus it supplies a boundary operation, not the missing scalar separator.
