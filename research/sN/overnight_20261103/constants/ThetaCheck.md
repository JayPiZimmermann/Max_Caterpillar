# Independent audit of the 175000 quadratic constant

The exact raw contract remains arbitrary real weights and biases in the
nine-parameter affine-skip model, exact MAX_N on every real input, N>=3,
and total original first-hidden width h1<=N^2. It concludes
h2>=N^2/175000. No local obstruction, statistical bound, normalization,
support moment, or coefficient-sign restriction remains in that contract.

## The stronger actual rate

`ThetaTwo.lean` strengthens the original matching-moment rate by counting
actual isolated gap slots. Outside the new bad event there are at least
7K/10 such slots. The imported all-graphs matching moment has exponent

    -(7/12) J |E| / (m(m-1)),

where J is the cardinality of the actual injective isolated-slot layout.
Substituting J>=7K/10 gives the new rate 49K/(120m(m-1)). This is not an
assumed independent-coin model or a numerical change to the old rate.
`rankIsolatedSlots` and `enumeratedSlot` supply the actual layout and its
injectivity; `rankIsolatedGaps` is the same set used by the new rank event.

The tail edge-count shift is handled after bounding the exponent using
the nonnegative actual edge count. The later replacement |E_tail|>=eta-d
multiplies by a negative coefficient and therefore has the correct direction,
including eta-d<0. The selected matching bound and the exact two-edge
exponential envelope are then combined with this rate.

`ThetaTwoActual.lean` averages the same actual configuration sample space:
the full permutation, tail-order permutation, and rank permutation. It
retains the new bad-event indicator during the averaging and invokes the
previous actual recording-fiber rank theorem at each fixed full/rank pair.
It counts original second-hidden indices; no expansion of the network is
charged as if it preserved width.

`ThetaTwoTransfer.lean` reconstructs the actual coverage proof with the new
rank event. Outside the original first-support and interference bad events,
the generic localization supplies an original zero-preactivation neuron
with a selected two-edge matching. The new rank-event exclusion is included
in that same neuron's event. The uniform union bound uses its exact finite
configuration fraction. Thus the stronger rate is actually connected to
the MAX representation, not merely to an abstract graph theorem.

## Probability and numerical assembly

The literal uniform-permutation bad event is fewer than 7K/10 isolated
nonanchor gaps. Its proved second-moment bound is at most 1250/m for
K>=50 and 10K<=m, hence at most 1/16 for m>=20000. The driver expands this
actual predicate and supplies no probability or moment hypothesis.

The chosen K=floor(m/10) satisfies these hypotheses. The simultaneous
actual half model has 16L<=105h1 and 8M<=h1 on one selected set, preserving
both original hidden index types. With N^2<=4.1m^2, it supplies L<=27m^2
and M<=m^2. Coverage is at least 5/8, and the new event envelope is at most
261/K^2. Since m^2<=101K^2, the model bound h2>=m^2/42200 follows. The raw
rounding loss is at most 4.1, so 4.1*42200=173020<175000.

The small branch 3<=N<=50000 follows from N<=2h2+2. N=50001 is the first
odd dimension in the large branch; n=25000 and m=24995 satisfy all cutoff
conditions. `ThetaCheck.lean` constructs actual caterpillar witnesses at
N=3 and N=50001, retaining the large second width symbolically.

No mathematical or model-bridge gap was found in this audit. The check file
has six exact named contracts. Source-bound kernel and axiom verification,
including this driver and the actual event modules, is performed by the
parent's reproducible verification gate; this prose is not itself that gate.
