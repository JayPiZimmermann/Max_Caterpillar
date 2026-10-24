# A smaller certificate for the natural eight-feature first hidden layer

The independently certified bound is unchanged: for the natural first
hidden layer with six functions
`sigma(u), sigma(v), sigma(u-v), sigma(s), sigma(t), sigma(s-t)` and the
two opposite reference-coordinate functions, the second hidden layer
requires at least seven neurons. No matching construction is known.
The model bridge and exhaustive real-parameter domain are those in
`overnight_fixed_natural8.md`. This new route leaves its checked artifacts
unchanged.

The original certificate used 26 generic top-tie locality equations and
24 equations obtained by eliminating the first-layer remainder at Boolean
rays. Only one of the latter is needed. If `p_j` and `q_j` are the
coefficients of `sigma(u-v)` and `sigma(s-t)` in outer preactivation `j`,
and `d_j` is its output sign after absorbing its magnitude, that equation is

    sum_j d_j (abs(p_j+q_j) - abs(p_j) - abs(q_j)) = 0.

It is the combination of rays
`1_{0,1,3} - 1_{0,1} - 1_{0,3}`. Each of the six first-layer functions
vanishes under this combination, as does the target, so the free remainder
disappears. Writing `sigma(z)=(z+abs(z))/2` also removes the linear parts
of all outer preactivations. Thus the equation applies to the complete
real coefficient domain, including zeros and sign boundaries. Its summand
is zero when `p_j*q_j >= 0` and is `-2 min(abs(p_j),abs(q_j))` otherwise.

Among the 54,688 old proofs, 54,038 already used no other ray equation.
`overnight_fixed_natural8_reduce_equations.py` produced rational replacement
witnesses for the remaining 650. The merge producer writes a separate
compressed proof. The independent checker reconstructs all equations,
asserts the three-ray identity explicitly, checks every rational Farkas
witness, and covers all 3,418 unordered flat quadruples and all sixteen
output-sign assignments, including repeated flats and zero boundaries.

The complete fresh check passed in 6.99 seconds. No circuit inequalities
or sign trees occur. In fact the resulting witnesses use only eighteen
of the locality equations, plus this one ray equation; the simpler
description above retains the uniform family of 26 locality equations.
This is an independently checked finite certificate, not a Lean proof.

To check the reduced route from this directory:

    python3 overnight_fixed_natural8_coverage.py
    python3 overnight_fixed_natural8_compact_verify.py

The compact checker imports only the independent exact checker modules
and Python's standard library. It does not import the LP producer or
trust its feasibility verdicts. `overnight_fixed_natural8_compact_check.json`
records the checked hashes and coverage count. The original proof hash
and original manifest remain intact.
