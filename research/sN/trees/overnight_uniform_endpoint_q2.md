# Endpoint Q2: exact rational relation, independently reviewed and replayed

The exact certificate proves a 36-term generic Fourier-kernel identity with
nonzero Q2 pairing **−448**. Independent semantic review and a fresh isolated
replay passed. A separate implementation recomputed the Q2 score by enumerating
signed connected vertex orders. This refutes the proposed Q2 functional on
the generic rational quotient, even for endpoint units. It is not a
whole-function identity: a nonzero lower-filtration remainder is allowed.
The unrestricted exponential lower bound remains open.

## The precise identity

Let `units` be `overnight_uniform_q9_inventory.json` and let
`results[1].proposals[0].integer_proposal` in
`overnight_uniform_endpoint_q2.json` give the integer coefficients. There are
36 nonzero coefficients, **no maximum/target column**, and the asserted identity
is the zero sum of the corresponding **unaveraged full S9** canonical kernels.
For apex frequency a and rooted child cuts q_e, our convention is

    R_U = (-a)^5 product_e 1/[q_e(q_e + epsilon_e a)].

Here epsilon=+1 when the oriented edge points from the child to its parent.
All 36 units are endpoint units: every epsilon=−1 child cut is a singleton.
The gate originally found this relation in the immutable existing 3400-row
modular evaluation matrix. The argument below certifies an identity in the
actual rational-function space and does not infer identity from those samples.

## Exhausting the poles

Every individual denominator factor is either an ordinary subset sum or a
singleton diagonal omega_i−omega_j. Each ambient factor occurs at most once in
each kernel. The unaveraged full label sum is invariant under all permutations.
A transposition i↔j fixes its diagonal pointwise and reverses its normal, so a
symmetric rational function with at most a simple pole has zero diagonal
residue. Thus no singleton diagonal can remain.

Modulo the total-sum relation, an ordinary subset and its complement define the
same hyperplane. The noncoordinate types for nine labels are exactly subset
sizes 2,3,4. `overnight_uniform_endpoint_q2_residue.py` explicitly sums all
actual-apex placements and all permutations, and forms each first residue as
an exact rational dictionary. It never discards another-apex contribution.

`overnight_uniform_endpoint_q2_dfs.py` proves these three rational residues zero.
Each record is a power of one primitive linear numerator divided by a list of
primitive linear denominators, with an exact rational coefficient. At every
node it cancels common factors and combines identical records. Above dimension
3 it checks that every displayed denominator has only simple poles. It then
checks one representative of every remaining pole orbit. Below dimension 4 it
checks the complete common-denominator numerator using exact FLINT arithmetic.
If all principal parts vanish, the rational function is polynomial; its
strictly negative homogeneous degree makes that polynomial zero.

The symmetry reduction uses a subgroup that fixes every preceding residue
normal, not the full label group after arbitrary restrictions. Initially the
cells are the two blocks defining the first cut. At each further residue,
every existing cell is refined by equal coefficients of the new normal in
physical-label coordinates (dependent labels have coefficient zero in the
chosen representative). Permutations within the refined cells fix all prior
normals and the new normal pointwise. Frequency charts are updated by exact
linear substitution. If an orbit contains a hyperplane absent from all displayed
denominators, invariance shows that the entire orbit has no actual pole. No
claim that a displayed denominator necessarily survives is used.

The completed fresh runs have 109 nodes for size2, 66 for size3, and 62 for
size4. Their receipts bind the source and exact fraction-cache hashes. Memo
files are reproducible acceleration artifacts; a fresh independent replay must
remove/rename the corresponding memo first, so its event record is complete.

## The final coordinate constant

After the preceding pole elimination, the original function has only simple
coordinate poles. Multiplication by product_i omega_i therefore makes it a
polynomial. Its homogeneous degree is zero, hence it is a constant c.

`overnight_uniform_endpoint_q2_constant.py` determines c without another large
rank calculation. Four fixed-coordinate residues preserve c and reduce the
arity from9 to5. For N≥6 the actual-apex coordinate residue vanishes; the
nonapex residue is the signed leaf-deletion rule. If the current head is a leaf,
the positive adjacent edge permits the exact root slide first. Deleting a
nonroot leaf contributes −epsilon times the smaller canonical kernel. Equal
unaveraged orbits are combined using their underlying tree and
kappa_v=outdegree(v)+1_{v=head}; these determine the same dictionary function.
The successive numbers of surviving orbit classes are20,12,6,4.

The final full S5 sum is evaluated with exact rational arithmetic at
(-40,1,3,9,27), away from every denominator. All480 summands sum to zero.
Consequently c=0. This completes the generic rational identity. Its independently
recomputed Q2 pairing −448 refutes the current Q2 score even on endpoint units;
it does not refute the desired matching or outward-twin separation theorem.

## Independent validation

Run `python3 research/sN/trees/overnight_root_endpoint_q2_replay.py` from the
repository root. It regenerates all three exact fraction dictionaries in a
temporary directory, compares their full contents, and reruns every recursive
proof without saved memo entries. The fresh proof visits 109, 66, and 62 nodes
and independently replays the final coordinate-constant calculation. It keeps
the frozen producer artifacts unchanged. This is a fresh replay of reviewed
producer code, not a separately implemented symbolic algebra system.

Run `python3 research/sN/trees/overnight_root_endpoint_q2_score.py` for the
separate standard-library implementation of the score calculation. It uses
explicit signed connected orders, without the producer's feature-vector code.
The JSON receipts bind the input hashes. These are exact computational and
written proofs; no new Lean theorem is claimed.

A second [semantic review](overnight_upper_endpoint_q2_review.md) checks the
pole-completeness and symmetry arguments. Its standard-library checker,
`overnight_upper_endpoint_q2_check.py`, independently computes the coordinate
residues directly, without root-slide preprocessing or colored-tree grouping.
The resulting 5,760 exact summands again give zero.

## Scope of the files

The modular endpoint gate is diagnostic; the three first-residue producers,
recursive exact pole proofs, and final coordinate constant are the proof.
`overnight_uniform_endpoint_q2_coordinate.py` is an earlier one-step reduction
and supplies only its colored-tree canonical key to the final constant script.
The older unnumbered DFS and `reduce` outputs are superseded and are not in the
frozen manifest. Raw input evaluation matrices and reproducible memo caches
are excluded. Compressed first-residue dictionaries are retained so the exact
recursive proof can be replayed directly.
