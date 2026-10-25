# A uniform head-motion gauge with controlled geometric corrections

This is a positive closure lemma for the live sparse cyclic family.
It changes head marks within a graph and keeps every correction explicit.
It is not a product-intertwining theorem or an exponential construction.

Assume $N\ge3$ throughout. The exact identities also hold at $N=2$,
but preservation of the top class uses $L_1\subseteq L_{N-2}$ and
therefore requires $N\ge3$.

Let $G$ contain the complete star at a label $b$.
Permit both signs of the canonical head $x_r-x_b$, and all five states
of each graph edge: absent, either frozen linear orientation, or either
free positive-part orientation. Allowing both head signs is exactly
adjoining global input reflections, since the other edge states already
permit both orientations. It costs only a factor of two.
More explicitly, writing the frozen linear forms as $f_e$ and the free
linear forms as $p_e$, define
$$
 F_{s,f,p}(x)=\sigma\left(s(x_r-x_b)+\sum_e f_e(x)
                                      +\sum_e\sigma(p_e(x))\right).
$$
Then $F_{-1,f,p}(x)=F_{+1,-f,-p}(-x)$ exactly. Negating each frozen form
and reversing each free orientation uses the same five states and the
same graph. No top-class parity argument is needed here.

## Every head-subset state of a contained tree stays in the family

Let $H\subseteq G$ be a spanning tree, choose an orientation
$t_e=x_u-x_v$ for every edge, and for a nonempty $I\subseteq E(H)$ put

\[
 V_I=\sigma\left(\sum_{e\in I}t_e+
                     \sum_{e\in E(H)\setminus I}\sigma(t_e)\right).
\]

Every $V_I$ belongs literally to the reflected five-state family on $G$.
To see this, choose $uv\in I$. If one endpoint is $b$, it supplies a
signed canonical head directly. Otherwise the tree cannot contain both
$bu$ and $bv$, because those edges together with $uv$ would form a cycle.

If $bv$ is absent from $H$, write
$x_u-x_v=(x_u-x_b)+(x_b-x_v)$.
If $bu$ is absent, write
$x_u-x_v=-(x_v-x_b)+(x_u-x_b)$.
The extra star edge is absent from **all** of $H$, so it does not overlap
any free or already frozen edge. Freeze the other edges of $I$ and leave
the complementary edges free. No coefficient doubles and no new edge
or head alphabet is needed beyond reflection.

This is a whole-function membership statement, not merely a top-class
reflection argument.

## Exact head exchange and centering

Write $m=|E(H)|=N-1$ and $U_e=V_{\{e\}}$. The exact cube-cover identity is

\[
 \sum_{\emptyset\ne I\subseteq E(H)}
    (-1)^{|I|+1}V_I=\sum_{e\in E(H)}\sigma(t_e).
\]

Indeed the cube is the union of the pyramids over its facets whose
corresponding coordinate equals one. An intersection indexed by $I$
is the pyramid with every coordinate of $I$ at the common maximum;
its support function is precisely $V_I$. Inclusion–exclusion proves
the identity, and linear precomposition preserves it.

Define the mean-zero head-mark state

\[
 \widehat U_e=U_e-\frac1m\sum_{f\in E(H)}U_f.
\]

Then

\[
 U_e=\widehat U_e+\frac1m\sum_f\sigma(t_f)
       +\frac1m\sum_{|I|\ge2}(-1)^{|I|}V_I.
\]

All these terms remain in the same reflected five-state graph family.
For $|I|\ge2$, the pyramid defining $V_I$ has dimension
$m-|I|+1=N-|I|\le N-2$. Thus centering the head mark preserves the
top class, with at most $2^{N-1}$ explicit lower-dimensional corrections.
The coefficient $1/(N-1)$ is genuinely arity-dependent.

## Count and remaining bridge

For the apex-star/twin-BST candidate, $|E(G)|\le3N-5$.
For a fixed graph and fixed star centre $b$, all reflected formal states
number at most $2(N-1)5^{|E(G)|}$. Allowing every eligible centre gives
the safe bound $2N(N-1)5^{|E(G)|}$, and the twin pairs have an
exponential count (at most $16^{N-1}$ per centre). The head-motion operation above selects states
already in that finite dictionary. It does not create a hidden
permutation closure or require repeated expansion to define its support.

This gives an actual geometric realization of a mean-zero head-mark
module, including its boundary corrections. It is compatible with
seeking a marked Eulerian operation, whose commutator coefficients
also sum to zero. It does not yet show that the Baxter shifted-shuffle
product or coproduct acts on these states, nor that the simplex is
represented by them at every arity.
There are only $m-1$ independent centered head states because
$\sum_e\widehat U_e=0$. The stated correction count concerns one exact
head-centering operation; it is not a bound on the accumulated width
of an iterative construction.

The adjacent checker verifies all tree head subsets and orientations
for complete-star-plus-path graphs at $N=3,\ldots,6$, and the cube identity
on every sign vector through six generators. These are finite convention
controls; the graph argument and cube-cover proof are uniform.
