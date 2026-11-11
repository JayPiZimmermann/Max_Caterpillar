# Improving the unconditional quadratic constant

Live target: for every N≥3, an exact real affine-skip two-hidden-layer network
with total first hidden width h₁≤N² satisfies h₂≥N²/650000. This has the
same scope as the published N²/10000000 theorem. The assembled declaration and an independent literal nine-array contract
have passed Lean; the content-bound rebuild gate is being run. It is not yet
a published theorem.

Three independent scalar/combinatorial improvements are used:

1. The actual fourth falling support moment is averaged directly:
   max_r (r)_4/2^r=105/16, attained at r=7,8. Averaging r⁴ instead had cost81/4.
2. The selected two-edge moment uses y²exp(-y)≤4exp(-2), rounded to4/7.
   This saves a factor7/2 over using a single exponential-series term.
3. For K≥82, fewer than K/2 isolated selected gaps forces at least10K/41
   selected adjacent pairs. The same exact first-moment argument therefore
   bounds the bad-rank fraction by41K/(10m), improving8K/m.

With K=floor(m/12), m≥100000, non-braid row count M≤5m² and falling moment
L≤27m², the literal coverage expression is at least9/20; the per-neuron
cost is at most465/K². The half restriction preserves both original hidden
index types and computes actual MAX on every real input. The existing proved
H(5,2) obstruction is supplied internally. Small arities use the already
verified linear bound N≤2h₂+2.

Evidence is recorded by separate Lean logs and exact-type checks. No
structural conjecture is assumed, and no production source was modified.

Further branch: replace the isolated-gap Markov estimate by a variance or
finite concentration bound. For K/m near1/8 the event is far below its mean,
so a uniform small failure probability should permit a larger cutoff. This
branch is independent of the first checkpoint and must pass actual finite
permutation semantics before being used.

A one-of-three coordinate restriction was also costed. Its sharp falling
moment is40/81, but with the current41K/(10m) failure estimate the additional
arity loss makes the optimized constant worse than the half restriction.
It should be revisited only if the bad-rank estimate is substantially improved.
