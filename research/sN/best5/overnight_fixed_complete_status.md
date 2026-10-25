# Complete-comparison three-unit frontier

**Live target:** max of five coordinates, modulo a shallow remainder from
the complete comparison span, as three outer ReLUs whose preactivations
belong to that same span. A successful construction compiles to widths
(16,5) and would match the existing lower bound for that fixed first
hidden layer. The unrestricted second hidden layer bound remains 4..6.

**Current outcome:** no construction and no complete K3 infeasibility
certificate. The principal advance is the independently reviewed uniform
mixed-chamber theorem. It replaces a huge necessary flat enumeration by
an exact finite formula in 42 unrestricted real coefficients. The K2
case now has a short analytic proof, using the cited braid-conforming
theorem. The original finite K2 certificate remains unchanged.

## Exact domain and final solver formulations

`overnight_fixed_complete_decide_smt.py` represents each preactivation in
the fourteen-dimensional invariant span: ten sigma(x_i-x_j), i<j, and
four differences x_i-x_4. Output magnitudes are absorbed into the
preactivations. Both sign counts (+,+,-) and (+,-,-) are retained.

The shallow remainder is eliminated by Boolean quadratic interpolation.
Its residual value h(S) determines c_i=h({i}) and
q_ij=h({i,j})-c_i-c_j; the sixteen equations for |S|=3,4,5 require
h(S)=sum c_i+sum q_ij. The value h([5]) is zero because the separate
reference term x_4 supplies the common-translation slope.

On each of all 120 braid cones, the formula imposes the following closed
disjunction: all three forms have weak fixed sign, or two opposite-output
forms agree up to sign on all four chain rays and the third has weak fixed
sign. The mixed-chamber theorem makes this necessary. It is also sufficient,
together with the Boolean equations: the total output is linear on each
cone, and agrees with the target on its generating rays. Zero forms and
boundary signs are included. No coefficient alphabet or numerical cutoff
is imposed. A rational SAT network must still pass the independent
whole-domain physical checker.

The model also contains the generic triple/quadruple locality covers and
26 redundant mixed-absolute necessary equations. Both full sign cases
timed out (p2 at300s; p1 at180s). These timeouts imply nothing about
feasibility. The parent ran a second solver independently.

`overnight_fixed_complete_symmetry_smt.py` removes the redundant
mixed-absolute equations, retains the covers, and adds a stronger exact
symmetry choice. Within the majority-output-sign class, select a
preactivation and comparison coefficient with maximal absolute value;
permute labels and same-sign neurons so this is the first coefficient of
the first such neuron, and flip that preactivation if necessary. All other
comparison coefficients in that sign class are bounded by this selected
coefficient in absolute value. This is a representative choice, not an
absolute bound. The zero case is included. The p2 run timed out at180s.

## Independently checked controls and closed routes

The known (10,6) network embeds into the complete comparison first hidden
layer and satisfies the complete model. Its compiled (16,6) network passes
the exact braid-cone verifier. The small conforming max4 control also passes.

The local-equations-only four-tie-zero model is insufficient: its exact
candidate satisfies all Boolean and generic locality equations, but gives
25/8 at (4,2,3,1,0), where the target is4. The candidate and exact witness
are retained in `overnight_fixed_complete_edgelocal_p2*`. A future lower
bound cannot rely on those local equations alone.

Requiring every second-layer neuron to be braid conforming is impossible
at any width for max5, by Grillo--Hertrich--Loho. That construction branch
is closed by literature, not merely its solver UNSAT verdict. The current
pair-cancellation model deliberately permits off-braid interior walls.

The exact flat inventory contains10,703,779,537 unordered covering triples.
No exhaustive campaign over those triples was started. The four-tie-zero
edge-cover subfamily has142 coloring orbits under label and neuron
permutation; the independent checker expands these to all59049 assignments.
Its two whole-cone sign cases returned solver UNSAT, but those verdicts
are not promoted to a general K3 result.

Finally, fixing the negative preactivation to a positive arbitrary scalar
multiple of the known (10,6) negative core is impossible even when the
other two preactivations and shallow remainder are free in the full span.
The parent obtained an independent Ethos check of a cvc5 proof for this
**restricted shape**. Its proof and replay manifest use the separate
`overnight_root_complete_*` prefix. This restriction is not a reduction of
the full K3 problem, and no new unrestricted width bound follows.

## Reproduction and next residual

Run the Python producers from this directory. The solver scripts use Z3
from `/tmp/overnight_fixed_z3`; the retained SMT2 files permit a different
solver to replay the exact formulas. Each producer records its source hash,
SMT hash, time cap, scope, and result. The parent owns the independent cvc5
and Ethos replay package.

The remaining exact problem is to decide the two full real-parameter K3
formulas, or find a human obstruction beyond pairwise wall cancellation.
The arbitrary-first-hidden-layer K2 problem additionally retains the
interior activation mechanism described in
`overnight_fixed_interior_patching.md`; the complete-comparison argument
does not remove that mechanism for arbitrary directions.
