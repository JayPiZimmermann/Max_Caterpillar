# A spanning mixture with the original dictionaries

25 October 2026. This is a corollary of `overnight_read_degree.md`.

The same method allows arbitrary weighted graphs of any fixed maximum degree
Delta>=1 to be added to the caterpillar and rooted-star face dictionaries,
with no restriction on their number of cycles. The enlarged dictionary
still requires

    Z = Omega_Delta((1-q)^(-N/r) / N^(2/r)),
    r=Delta+1, q=(1/7)(6/7)^Delta.

Choose the original locality weight y=1/6, or vertex probability p=1/7.
The total target weight is W=(7/6)^N minus a quadratic truncation P_N.
An original dictionary function contributes at most N-2 after weighting.
The moment argument above bounds an added graph's contribution by
W C_Delta N^(2/r)(1-q)^(N/r), for a constant C_Delta. Thus

    W-P_N <= |K_0|(N-2)
               + |K_1| W C_Delta N^(2/r)(1-q)^(N/r).

For fixed Delta>=1, (1-q)^(-1/r)<7/6. The second per-unit bound therefore
eventually dominates N-2, while P_N/W tends to zero. Divide by W to obtain
the stated exponential bound on Z=|K_0|+|K_1|. Added degree-zero functions
are shallow and can simply be absorbed into the remainder.

This corollary includes both original combinatorial constructions and new
weighted comparison graphs with arbitrarily many cycles. It remains a
dictionary width statement, not a lower bound for arbitrary first-layer
linear forms.
