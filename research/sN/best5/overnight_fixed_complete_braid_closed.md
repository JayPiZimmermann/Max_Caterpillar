# Closed route: conforming second-layer units cannot construct max5

The whole-braid sign-stable K3 construction gate is closed by a known
arbitrary-width theorem. It must not be resumed by enlarging widths or
running the other output-sign choices.

Grillo, Hertrich, and Loho define conformity at every neuron, prove the
quotient correspondence between the five-coordinate braid fan and its
four-dimensional zero-coordinate version in Lemma3.1, and exclude max5
for two conforming hidden layers in Theorem5.2. The primary source is
[Depth-Bounds for Neural Networks via the Braid Arrangement, arXiv v2](https://arxiv.org/html/2502.09324v2#S5).

Our gate required each preactivation to have one weak sign on every
braid chamber. Each folded core unit therefore satisfies their conformity
hypothesis. Although the particular opposite-head compiler could introduce
extra walls, this does not evade the theorem: restrict the reference
coordinate to zero and implement the shallow remainder by passing its
individual nonnegative first-layer features through the second layer.
This gives a conforming implementation at some finite width, which the
theorem excludes.

The completed K3 test returned solver-UNSAT in51.6 seconds. That diagnostic
is unnecessary for closure; the cited theorem supplies the mathematical
reason. Its N4 positive control passes the independent global verifier.

A valid construction must instead retain off-braid walls in individual
second-layer units and cancel their contributions in the output. For a
complete comparison first layer the shallow remainder cannot cancel an
interior wall of a braid chamber. Hence every such wall needs both output
signs among the folded core terms. All-positive and all-negative cores are
excluded by this observation together with the cited theorem.

The current constructive gate permits exact pairwise cancellation on each
chamber. It retains weak and zero boundaries and leaves arbitrary real
coefficients unbounded. It excludes genuine three-way proportional
cancellation and therefore cannot provide an unrestricted K3 lower bound
if the solver rejects it.
