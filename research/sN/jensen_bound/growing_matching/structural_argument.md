# Actual-model hypothesis for the growing-matching route

The new hypothesis `LocalMatchingObstruction k q`, or H(k,q), concerns only
actual homogeneous normalized networks computing `MAX_k` on all real inputs.
Their first dictionary consists of zero-sum rows with support at most two,
including the rows used by the one-layer output. All coefficients, output
signs, and linear skips are arbitrary real numbers. H(k,q) says that some
outer neuron's actual signed braid interaction graph contains q pairwise
vertex-disjoint ordinary edges.

There is no random event, probability, counting bound, or proposed asymptotic
conclusion in H. It is the remaining local structural theorem needed for the
growing-arity route.

The transfer theorem starts from an actual normalized `MAX_N` model, keeps
k selected coordinates, and uses the caller's actual complementary-tail gap
point. The proved dominant-gap threshold gives literal localization masks,
all-input `MAX_k` equality, and translation normalization. If no original
support of size at least three is contained in the keep set, the actual local
first dictionary is braid/zero. H therefore supplies a local q-matching.

For q>0, the matching contains an actual nonzero edge. An original outer gate
which is not zero at the localization point has every local W coefficient
zero. Consequently the matching's outer slot is an original surviving slot,
with its original preactivation zero at exactly that point. The proved signed
edge-weight identity identifies its local graph with the comap of the
original ambient graph. Injective unordered-edge transport preserves the
cardinality q, all parallel-row cancellations, vertex disjointness, and
membership in the actual selected coordinate set.

This supplies both a direct selected-matching-event witness and a standalone
actual-threshold theorem. No local-model, graph-correspondence, or genericity
hypothesis remains in the latter.

Two checks calibrate the precise hypothesis. The independently closed real
star certificate proves H(5,2) without any new premise. Conversely an actual
normalized linear `MAX_1` model with no hidden neurons proves H(1,1) false.
Thus H is substantive; defining it does not establish it for growing k and q.

Production: `GrowingMatching/Structural.lean` and the separate
`GrowingMatching/FiveInstance.lean`. Expanded actual-model/control checks:
`verification/frontier/CountGrowingMatchingStructuralCheck.lean`. The receipt
is `structural_receipt.json` in this directory. A growing-arity quantitative
improvement remains conditional on a corresponding H(k,q) theorem.
