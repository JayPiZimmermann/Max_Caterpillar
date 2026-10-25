# A bounded triangle-product homotopy

Let `u,v` be the two nonzero vertices of an oriented triangle based at
zero, and put `b=v-u`. Write `E_u,E_v,E_b` for its unit cubical edges
and `g_u,g_v,g_b` for translation. The triangle cycle is

\[
 \Gamma=E_u+g_uE_b-E_v.
\]

Doubling followed by subdivision satisfies the exact cubical identity

\[
 S\Gamma-2\Gamma=dP,
\qquad
 P=g_uE_u\wedge E_b-E_u\wedge E_v-g_uE_b\wedge E_v.
\]

Thus `P` consists of only three squares. Equivalently,
`P=E_v wedge Gamma+g_u E_u wedge E_b`. Both statements hold for any
triangle attachment and reflection, with their actual orientation signs.

For a product `Y=Gamma_0 ... Gamma_(k-1)` of closed degree-one cycles,
the following is an explicit primitive of `(S-2^k)Y`:

\[
 \sum_{i=0}^{k-1}(-1)^i2^i
 (\Gamma_0\cdots\Gamma_{i-1})P_i
 (S\Gamma_{i+1}\cdots S\Gamma_{k-1}).
\]

Leibniz gives the sign `(-1)^i`; the resulting sum telescopes. Since
`Gamma`, `P`, and `S Gamma` have at most 3, 3, and 6 edges/squares,
the total number of cubes before cancellation is
`3^k(2^k-1)<6^k`. This is a uniform bound for this single product-homotopy
step. It is not a closure theorem under the next ordered facet operation.

For the explicit ordered boundary
`Y_4=-A B`, where
`A=Gamma_(012;root2,-)` and `B=Gamma_(234;root2,+)`, one may choose

\[
 X_4=P_A S(B)-2A P_B.
\]

Its exact boundary is `(4-S)Y_4`. The producer
`overnight_upper_ordered_product_homotopy.py` checks all local signs
and this complete chain identity. It gives 27 cubes for `X_4`, compared
with 48 from the generic star-Koszul contraction. The next ordered
boundary has 104 cubes; a generic corrected filling gives 2,116 cubes.

The generic contraction also fails a tempting simplification: on the
actual ordered 48-cube `X_4`, `H S X_4` has 188 nonzero cubes, although
`H X_4=0`. Therefore the contraction image is not preserved by doubling.
This exact control is recorded in `overnight_upper_ordered_doubling.py`.

The newer augmentation-correction route in
`overnight_upper_ordered_augmentation.md` avoids doubling altogether.
The three-square homotopy remains a useful explicit nonproduct state,
but neither route currently controls total support by `C^n poly(n)`.
