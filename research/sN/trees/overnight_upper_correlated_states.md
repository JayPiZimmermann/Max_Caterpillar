# Correlated max-substitution: complete fixed-path boundary

25 October 2026. These tests retain the local vertex-split source catalogue
from `overnight_upper_baxter_bridges.md`. They introduce no new graphs,
head values or numerical alphabet.

First take the two-edge orientation-difference cycle

\[
 F(t,u,v)=\sum_{\epsilon,\eta\in\{-1,1\}}
   \epsilon\eta\,
   \sigma\bigl(t+\sigma(\epsilon u)+\sigma(\eta v)\bigr).
\]

Its total coefficient and its signed inner preactivation both vanish
identically. Consequently its two outer tails cancel, and remain cancelled
after any common coordinate substitution $S_a$.
This removes the formal-offset obstruction, but it does not make the
local tree rule valid. For the four-input path with head $x_1-x_0$ and
edges $12,23$, substitution at labels $1,2,3$ gives exact gaps
$80/81$, $80/81$, and $44/45$, respectively.
The source rank bounds are the previously checked global rational
identities; fresh modular augmented rows certify the strict gaps.

The stronger four-channel test adds the substituted targets of all four
orientations separately. At the endpoint split, source rank is $44$ and
adjoining those four targets gives rank $48$. Thus **no nonzero
orientation combination on this fixed head and graph** lies in the local
source span. The zero-tail condition does not change that conclusion.

Finally allow every canonical head placement and every orientation on
the full four-vertex path $01,12,23$. The 24 descriptions have rational
span dimension $8$: a modular rank-$8$ minor and 16 independent exact
null relations prove both bounds. Their substituted image together with
the local source family has rank at least $48$, while the source has
exact rank $44$. Hence the intersection has dimension at most $4$.

There is an explicit four-dimensional subspace attaining that bound:
the old units in which the split endpoint is the isolated apex.
Writing their head coefficient at that endpoint as $s\in\{-1,1\}$,
their substituted top class is a single new unit with coefficient $s$.
For $s=-1$ add the free edge form $x_a-x_{\rm new}$; for $s=1$ add
$x_{\rm new}-x_a$. The two omitted terms in the scalar identity each
ignore one coordinate and are lower-dimensional. Every one-term
identity is checked exactly, and the four-dimensional independence
is checked by evaluation.

Therefore, within this complete fixed-path input space, the local split
rule closes **exactly the isolated-apex subspace**. Mixing orientations
or moving the head within that path does not create another valid state.
This is a finite structural exclusion, not a theorem against
graph-mixed cancellation cycles or the sparse cyclic candidate.

The records are `overnight_upper_correlated_split.json`,
`overnight_upper_correlated_channels.json` and
`overnight_upper_correlated_head_closure.json`, with their producers
and bounded logs. The first split attempt stopped on a tuple/list
comparison in a provenance assertion; the corrected second run passed.

The next viable target must mix underlying graphs, use a head-dependent
geometric state, or work directly with a coherent sum representing the
simplex. Even constant support growth would require appropriate
arity-dependent coefficients; no fixed scalar rewrite alphabet is
being claimed as a uniform maximum construction.
