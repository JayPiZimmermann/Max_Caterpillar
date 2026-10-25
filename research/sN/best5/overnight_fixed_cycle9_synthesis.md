# Five-cycle synthesis: exact controls, no construction yet

The live target is a physical `(9,6)` representation of `max5` using five
oriented C5 comparisons and the four features `σ(x0), σ(-x0), σ(x2), σ(-x2)`.
No new representation or lower bound is established in this package.

The unrestricted minimum second hidden layer width at N=5 remains between
four and six. The lower bound is the Lean-verified general theorem
`N+2 <= 2*h2` in `frontierN/overnight_general_antipodal.lean`; the upper
bound is the existing `(10,6)` network. The fixed-ten optimum six and the
fixed-P4 lower bound seven do not establish an unrestricted bound of six.
The proved minimum first hidden layer width nine remains unchanged.

## Constructive invariant-core model

The first search uses `max5-x0 = R + sum d_k σ(g_k)`, with four terms and
`R,g_k` in the span of the five comparisons and `x2-x0`. It compiles into
a physical `(9,6)` network with two opposite neurons for the head. This
is an upper-bound search restriction. It is not a reduction of arbitrary
four-carrier physical networks to four invariant core terms.

The exact necessary system has31 Boolean input-value equations and26
mixed-absolute-value equations at generic top ties. All real coefficients
are unbounded. A sign flip of a core preactivation is absorbed into R;
permuting neurons with the same output sign is also harmless.

The point-counterexample loop produced15 rational candidate networks,
each refuted by an exact input, then hit a30-second solver limit. The
counterexamples rapidly acquired large denominators; this is a failure of
the refinement mechanism, not evidence for a limiting representation.

A second loop adds an entire first-layer comparison-cell identity on a
failed cone. Every preactivation there either has fixed sign, carries the
known target hyperplane, or belongs to a cancelling spurious group. A
necessary linear relaxation imposes zero signed sum of oriented gradients
on the latter. Revisiting such a cell adds pairwise collinearity and common
orientation, expressed as vanishing2x2 minors and nonnegative dot products.
These conditions cover zero gradients and all sign boundaries. They do not
bound ratios or magnitudes. The exact quadratic solves timed out after40
seconds for orientation representative2 and30 seconds for representative1.

For representative0, the original necessary system was solver-UNSAT for
both2-positive/2-negative and3-positive/1-negative output signs, in0.5 and
2.8 seconds respectively. No independent infeasibility certificate was
exported, so these remain diagnostics. Representatives1 and2 remain open.

A third necessary system uses derivatives at a strict braid point x. Write
`z_k=g_k(x)` and let `a_k` be the local input gradient of g_k. If the target
is linear near x, the odd part of the directional derivative gives

```
grad R + sum_(z_k>0) d_k a_k + (1/2) sum_(z_k=0) d_k a_k
    = grad(max5-x0).
```

Its even part gives `sum_(z_k=0) d_k |a_k·y|=0` for each tested direction y.
These remain necessary at zero outer preactivations; no arbitrary choice
of a derivative at zero is made. Adding the coordinate directions on all30
comparison cells hit a60-second solver limit before proposing a candidate.

`overnight_fixed_cycle9_counterexamples_verify.py` independently evaluates
all35 retained failed candidates across the core and physical loops with rational arithmetic.
It imports neither the search producer nor the global cone checker.

## Full physical model without an opposite head

`overnight_fixed_cycle9_physical_smt.py` uses all54 real second-layer weights
of a physical `(9,6)` network, with four positive and two negative output
weights normalized to±1. It does not impose an opposite head, paired anchor
coefficients, or invariant second-layer preactivations. Only permutations
within each output-sign class are used as symmetries. In particular a sign
flip of a preactivation is not treated as a physical-network symmetry.

Both translation ends supply necessary identities. Let v=±1, let a_k be
the kth preactivation at v, and let B_k(x) be its directional derivative:
first-layer rows active at v become linear; zero rows remain ReLUs. Then

```
sum_k d_k σ(a_k) = ±1,
sum_(a_k>0) d_k B_k(x) + sum_(a_k=0) d_k σ(B_k(x)) = max5(x).
```

A zero-base B_k is invariant under common coordinate shifts. The same26
generic-tie equations therefore apply, guarded by a_k=0. Active nonzero-base
terms are shallow and disappear under the higher mixed differences. The
model also enforces physical values at±1_S. The unrestricted physical
necessary model hit its60-second solver limit without a candidate.

A separate declared constructive branch has one active carrier at each
translation end and four common zero-slope neurons. The inactive slopes of
the two carriers are arbitrary nonpositive reals. Their full preactivations
need not be opposite, and the common zero-slope neurons may depend on the
common shift between the two ends. This branch produces exact candidates,
but its point-refinement loop again grows large rational coefficients and
retained15 exact failed networks before the180-second campaign limit, and
none passed a global check. Its failure does not exclude other physical
tail patterns or other output-sign counts.

The appropriate reopening condition is a new region-wide geometric
constraint or an analytically specified network. Further point-only
refinement of the same sequence is not the intended next step.

## Full-domain verifier and independent controls

`overnight_fixed_physical_verify.py` checks the actual physical network on
all720 cones of the order arrangement of the five inputs together with a
fixed zero coordinate. No special output head is assumed. Every first-layer
feature is linear on a cone; its extreme rays determine whether an outer
preactivation has fixed sign. Interior hyperplanes are grouped by exact
proportional normals, their signed curvatures must cancel, and the remaining
linear gradient must equal the maximizing input coordinate. Continuity
covers every boundary. This is a sufficient global proof, not a sample test.

The verifier passes the known `(10,6)`, `(9,14)`, and two-anchor `(12,6)`
controls. A further `(10,7)` control replaces a linear head L by
`σ(L+c)-σ(-L-c)-σ(c)` with c one nonnegative first-layer feature. It has the
same function but a nonlinear head; the full physical verifier accepts it
without requiring the earlier anchor-pair convention.

`overnight_fixed_physical_tail_controls.py` independently compares the tail
formulas with actual rational finite difference quotients of these four
networks:272 quotient controls and208 generic-tie identities pass. The
known `(10,6)` network also passes the physical SMT constraints with its
weights fixed, followed by the independent720-cone global check.

The physical-tail model was independently reviewed by the other proof agent,
who confirmed the asymptotic interpretation, the zero-slope translation
invariance, and the locality guards.

All solver campaigns declare one thread, a3GiB address-space bound, finite
per-iteration limits, durable candidate files, and exact failed-input
witnesses. Timeouts and solver-only UNSAT outputs are search records, not
new mathematical certificates. All frozen earlier manifests remain intact.
