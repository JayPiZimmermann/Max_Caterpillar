# Necessary row-sum splits at the now-matched first width nine

For an exact two-hidden-layer network computing `max_5`, with arbitrary
real weights and biases and no skip connections, remove biases by
recession and classify first rows by positive, negative, or zero
coordinate sum. At first width nine, the only splits still possible are

\[
 (|J_+|,|J_-|,|J_0|)=(1,1,7)\quad\text{or}\quad(2,2,5).
\]

This is a necessary row-count statement, not a complete classification
of either family and not a second-width lower bound beyond the existing
ones.

The earlier support certificate gives `|J0|>=5`, and both signed classes
are nonempty. Its five-feature cell argument says that a singleton
signed class requires at least six nonzero zero-sum features.

The rectangle obstruction strengthens the latter conclusion to at least
seven. Suppose, for example, `J+` is a singleton and there are exactly six
zero-sum rows. Translation to positive infinity gives

\[
 \max_5(x)=\ell(x)+R(\Phi(x))+
          \sum_k d_k\sigma(g_k(\Phi(x))),
\]

where `Phi` consists of the six zero-sum ReLU features and `R,g_k` are
linear. Every negative-sum first row vanishes at this translation end,
regardless of how many such rows there are. Zero-slope second neurons
ignore the unique positive-sum row; passing second neurons contribute
only to the displayed linear remainder.

The exact six-row classification uses only this factorization and the
feature-fiber condition. It does not require the opposite signed class
to be a singleton. It therefore still forces the natural six invariant
features and `ell=e0`. The resulting finite shallow completion
contradicts `overnight_fixed_natural8_rectangle.md`. The argument at
negative infinity is identical when `J-` is a singleton.

Consequently, at total width nine a singleton signed class forces seven
zero-sum rows and exactly one row in the other signed class. If neither
signed class is a singleton, each has at least two rows and the zero-sum
class has at least five; equality of the total width forces `(2,2,5)`.
Zero rows or useless repeated rows cannot evade the count because the
support/factorization exclusions concern effective nonzero features.

The `(2,2,5)` alternative has not been excluded. In particular, it must
not be silently dropped when trying to prove an unrestricted lower bound
on the second width at first width nine. For the known nine-row P4 first
layer, the split is `(1,1,7)` and its separate second-width interval remains
`6<=h2<=14`.
