# A stronger matching bound for mixtures containing both constructions

25 October 2026. Uniform mathematical proof, independently reviewed; not Lean
verified. This improves the exponential base in the matching-mixture bounds
of `overnight_pseudoforest_matching.md` and `overnight_bounded_excess.md`.
It does not assert an unrestricted all-tree bound.

Let B be the paper's caterpillar and specified rooted-star face dictionaries.
Add arbitrary real-head, real-weight comparison pseudoforest units whose
graphs on all N labels have a matching of size at least k, with 0<=2k<=N.
Allow a shallow remainder, signed output coefficients, and biases. Write Z
for the number of terms in B and the added family. Put

    m=floor(N/4),  P_m=binom(N,m)(1/4)^m(3/4)^(N-m),
    rho=13/16,     d_k=1+3k/13+9binom(k,2)/169.

For N>=12,

    Z >= P_m (16/13)^k / d_k
      >= (16/13)^k / [(N+1)d_k].

In particular this elementary form gives
Omega((16/13)^k/[sqrt(N)(1+k^2)]). The companion coefficient addendum
sharpens the polynomial factor; the argument here proves the exact bound.

## Count at a single binomial mode

At each permutation locality of tied size m>=3, some counted unit must
contribute a nonzero top-dimensional class. After dividing the number of
localities by m!(N-m)!, a function in B covers at most 6^m. A weighted graph
unit can contribute only if its induced graph on the tied labels has at
most two components. The arbitrary-head and signed-weight germ argument is
unchanged from the weighted comparison-graph theorem.

Select labels independently with probability p=1/4. Give a pseudoforest an
auxiliary orientation of indegree at most one. On each of k disjoint matching
edges, the event that the parent is absent and child present has probability
3/16. These independent events lie in distinct induced components. Therefore
the probability that the graph has at most two induced components is at most
rho^k d_k. Its coverage at size m, multiplied by p^m(1-p)^(N-m), is bounded
by this unconditional probability.

For a base function the same weighted coverage is at most

    6^m p^m(1-p)^(N-m) = (3/4)^N 2^m
       <= (13/16)^(N/2) <= (13/16)^k.

The first inequality follows from m<=N/4: raising its exponential bases to
the fourth power reduces it to 162<=169. Thus, with K_0 base terms and K_1
added terms,

    P_m <= rho^k (K_0+d_k K_1) <= rho^k d_k Z.

The integer floor(N/4) is a mode of Bin(N,1/4), including the case of two
modes when N is congruent to 3 modulo 4. Its probability is at least
1/(N+1), and Stirling gives P_m=Theta(N^(-1/2)).

## Free canonical classes

The same argument permits either of these classes to be adjoined for free:

* all canonical star face functions, with every root, orientation, and face
  state, provided N>=20;
* all canonical tree face functions whose original tree has matching number
  at most two, again with every root, orientation, and face state, provided
  N>=28.

Here Z counts only terms outside the free class; assign overlapping terms to
the free class first. The existing exact five-label star separator, or the
exact seven-label matching-number-two separator, propagates to every tied
size m>=5, respectively m>=7. Apply that separator at each locality before
counting. A free-class term is zero under it; a remaining term can contribute
only where its previous top-class coverage test passes. Thus the same upper
capacities apply. The thresholds ensure floor(N/4) reaches the separator's
starting size.

These free classes have canonical unit-length comparisons and a canonical
root head. This statement does NOT adjoin arbitrary weighted or arbitrary
real-head stars for free.

## Additional cycles

For a graph G let b(G)=sum_C max(0,|E(C)|-|V(C)|). If every added graph has a
matching of size at least k and b(G)<=b, replace d_k by

    D_(k,b)=sum_(j=0)^min(k,b+2) binom(k,j)(3/13)^j.

Extend a maximum matching to a spanning forest and add one extra edge in
each originally cyclic component. The resulting pseudoforest omits b(G)
edges. Restoring these edges merges at most b(G) induced components, so a
covered tie has at most b+2 independent matching witnesses. The preceding
probability calculation now gives rho^k D_(k,b), and the rest is identical.

In particular k=Omega(N), b=o(N) yields

    Z >= exp(k log(16/13)-o(N)).

There is no maximum-degree restriction. The same two free canonical classes
and the same starting-size thresholds remain valid.
