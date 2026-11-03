# A quartic width product without an upper-width hypothesis

`TradeoffTheta.ordinary_width_product` states

    h₁ h₂ ≥ N⁴ / 700000

for every ordinary exact two-hidden-layer MAX_N network with N≥6.
`TradeoffTheta.affine_width_product` gives the same bound for arbitrary real affine
skips and biases with N≥15. Both count the original widths, with no upper cap
on either layer.

The proof combines the uncapped minimum tradeoff with the previously verified
first-width theorem. In the ordinary model, the latter gives h₁≥N²/4 for N≥6.
For affine skips, the existing exact encoding uses h₁+2N first slots; retaining
that loss still gives original h₁≥N²/4 for N≥15. Multiplying the minimum
tradeoff by h₁ then gives the displayed quartic bound.

This is a product bound. It does not force h₂ to be superlinear when h₁ is
allowed to be sufficiently large. In particular it is not an unconditional
exponential lower bound on the second hidden layer.

`ProductCheck.lean` checks the raw nine-array formula, the ordinary contract,
and actual caterpillar networks at the two boundary arities. The exact status
is in `product_receipt.json`; the prose alone is not a proof-status claim.
