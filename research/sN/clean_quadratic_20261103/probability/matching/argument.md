# A short matching estimate for the existential-constant proof

Status: complete elementary mathematical proof, matching the already Lean-verified
`MatchingSizeBias.matching_geometric_le_edges`. This note does not introduce a
new formal theorem or improve the constant. It removes the size-bias abstraction
from the paper presentation.

## Lemma

Let G be a simple graph on m vertices, m >= 2, with e edges. Choose uniformly
a matching M of size J, where 0 <= 2J <= m, and let X = |M intersect E(G)|.
For every 0 < theta <= 1,

    E theta^X <= exp[-2 J e (1-theta^3)/(3 m(m-1))].

In particular,

    E 2^(-X) <= exp[-7 J e/(12 m(m-1))]
                <= exp[-J e/(2 m^2)].

The empty graph and J=0 cases are equalities.

## Proof

Suppose J,e > 0. Generate M by putting a uniform random permutation of the
m vertices into m positions, and pairing positions (1,2), (3,4), ..., (2J-1,2J).
Every J-matching has the same number of such representations, so its law is
uniform. A fixed graph edge belongs to M with probability

    p = J / binom(m,2) = 2J/[m(m-1)].

For each fixed graph edge {a,b}, modify the permutation by first swapping a
into position 1 and then swapping b into position 2. Denote its resulting
matching count by X_ab. The new permutation is uniform conditional on having
a,b in positions 1,2: every pinned permutation has exactly m(m-1) preimages,
obtained by undoing the second swap with any source position other than 1,
and then undoing the first swap with any source position. Consequently the
new unordered matching is uniform conditional on containing {a,b}.

Only the first pair and the pairs containing the two original source positions
can change. Thus at most three matching pairs change, and pointwise

    X_ab <= X + 3.

Put F(z) = E z^X for 0 < z <= 1. Expanding X as a sum of edge indicators gives

    F'(z) = sum_{ab in E(G)} p E[z^(X_ab-1)]
          >= e p z^2 F(z).

The last inequality follows from X_ab-1 <= X+2 and z <= 1. Since F(z)>0,
integration from theta to 1, using F(1)=1, yields

    -log F(theta) >= e p (1-theta^3)/3.

Exponentiating proves the lemma.

## Why this is the preferred paper route

The complete proof is one coupling paragraph and one generating-function
calculation. It applies to every graph, including stars and graphs with very
high-degree vertices. No independence or negative-dependence assertion is
used. Its linear dependence on e in the exponent is exactly what is needed
to optimize the expression e^2 exp(-c K e/m^2) and retain a quadratic width
lower bound.

The proof is already formalized, with the same forcing map, in:

- `MaxCaterpillar/Frontier/RandomRestriction/MatchingSizeBias/Forcing.lean`,
  `forcingEquiv`: exact m(m-1)-to-one pinning construction.
- `.../Damage.lean`, `sampleCoupledCount_le`: three-pair damage.
- `.../Identity.lean`, `finite_size_bias_identity`: the indicator sum identity.
- `.../Laplace.lean`, `matching_geometric_le_edges`: the displayed result.

The Lean development uses an ordered edge and selected slot in its finite
sample space. The paper can pin to the first pair because pair labels are
forgotten after pinning, and every matching containing the forced edge has
the same number of pinned permutation representations. This is the same
conditional matching law.

## Alternatives assessed

1. **Independent edge indicators. Rejected.** Take m=4,J=2 and let G itself
   be a perfect matching. Then X=2 with probability 1/3 and X=0 otherwise,
   so E 2^(-X)=3/4. Treating its two edges as independent with probability
   1/3 would give (5/6)^2=25/36 < 3/4. Even exp[-E X/2]=exp[-1/3] is too small.

2. **Sequential exposure with a uniform lower bound on remaining density.
   Rejected as a direct argument.** After exposing an edge incident to the
   center of a star, no graph edges remain, although the initial density was
   positive. A density-depletion analysis is possible but longer than pinning.

3. **Bounded-difference concentration. Insufficient without extra ideas.**
   A direct Azuma-style lower-tail bound naturally has exponent of order
   (E X)^2/J = J e^2/m^4. This loses the linear dependence on e needed in the
   sparse-to-intermediate range. It is not a direct replacement.

4. **Adaptive two-pair forcing. Valid but unnecessary for the paper.** The
   newer `research/sN/overnight_20261103/matching_force/` route obtains
   X_ab <= X+2 by an adaptive choice of slot and proves the stronger constant
   3/4 instead of 7/12. The proof of the correct conditional law is longer.
   Retain it for numerical optimization, not the existential proof.

5. **Claim two-pair damage for the fixed-slot map. False.** Start from pairs
   (1,2),(3,4),(5,6), force (3,5) into the first pair, and let G have exactly
   the edges (3,5),(1,4),(2,6). Then X changes from 0 to 3. The bound +3 is
   sharp for this simple map.

6. **Black-box size-bias concentration theorem. Correct but less
   self-contained.** The one-line derivative argument above contains the
   whole needed theorem, so importing or defining an abstract theorem adds
   exposition without shortening the argument.

7. **Random perfect matching with independent thinning. Not a direct
   substitute.** It may simplify the sampling law, but conditional retained
   size fluctuates and the neuron-cover construction presently fixes J.
   Reworking that construction creates additional bookkeeping with no
   advantage over the uniform partial-matching lemma.
