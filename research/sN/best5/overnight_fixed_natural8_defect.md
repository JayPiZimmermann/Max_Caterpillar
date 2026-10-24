# Twenty-one inequalities replace all individual natural8 certificates

This is a new, independently checked route to the same research-only
bound: the natural first hidden layer of width eight requires second
hidden layer width at least seven. A matching construction is open.
The original proof, reduced proof, and their manifests are unchanged.

Let `E_0,...,E_25` denote the 26 generic top-tie locality equations in
`overnight_fixed_natural8.md`, and let

    delta = sum_j d_j (abs(p_j+q_j)-abs(p_j)-abs(q_j)),

where `p_j,q_j` are the coefficients of `sigma(u-v),sigma(s-t)` in
outer preactivation j. Matching the three rays described in
`overnight_fixed_natural8_compact.md` forces `delta=0`.

The new certificate proves a more informative intermediate statement:
**every four-neuron candidate matching the locality equations has
`delta <= -2`.** Hence its discrepancy at the negative corner is at
least one in the original ReLU normalization. This follows from the
same exhaustive flat cover over arbitrary real parameters, not from
an integer coefficient box or sampled sign regions.

The whole argument now uses 21 explicit equation combinations. Seventeen
yield a contradiction from the locality equations alone. The other four
are simply `delta+E_13`, `delta+E_14`, `delta-E_24`, and `delta+E_17`.
In a covered case, at least one of these 21 combinations has only
nonpositive coefficients on the independent nonnegative absolute-value
variables, while its required locality right-hand side is positive.
The four combinations involving delta all have locality right-hand
side two, and thus imply `delta <= -2`.

`overnight_fixed_natural8_templates.py` contains the explicit combinations.
It reconstructs their coefficients using the independent exact arithmetic
checker and enumerates all 3,418 unordered flat quadruples and all sixteen
output-sign patterns. This includes repeated flats and closed sign
boundaries. It imports no LP solver and reads neither the old proof nor
the new compressed per-case proof. No feasibility verdict is trusted.
Together with the independently checked flat coverage and the existing
model bridge, it is a complete finite certificate on the original real
parameter domain. It is not a Lean proof.

Reproduce it from this directory with:

    python3 overnight_fixed_natural8_coverage.py
    python3 overnight_fixed_natural8_templates.py

The companion JSON records hashes, the case count, and which inequalities
are used. The templates were discovered by inspecting certified Farkas
witnesses, but their discovery method is not part of this verification.
