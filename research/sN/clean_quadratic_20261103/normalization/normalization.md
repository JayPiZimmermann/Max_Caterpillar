# Elementary normalization and support regularization

This is a mathematical proof draft for the existential-constant paper theorem.
The starting architecture is an ordinary two-hidden-layer ReLU network, with
arbitrary real biases and no skip connections. The intermediate homogeneous
form contains linear and shallow terms introduced by exact algebra. The
original first- and second-layer index bounds are preserved throughout.

The draft gives a shorter route than the previous Lean implementation for
coordinate localization: a diagonal-preserving lift removes the need for a
second diagonal normalization. This step is now formalized in AnchorLift.lean
and AnchorLocalization.lean; its independent evidence is recorded separately
by recheck.py. The other manuscript lemmas here are mathematical arguments,
not new Lean declarations in this directory.

## 1. Biases disappear by recession

Write sigma(t)=max(t,0), e=(1,...,1), and

    F(x)=b_out+sum_k v_k sigma(b2_k+sum_j W_kj sigma(b1_j+A_j x)).

Assume F(x)=MAX_N(x) for every real x. For every t>0,

    F(tx)/t=b_out/t+sum_k v_k sigma(b2_k/t+sum_j W_kj sigma(b1_j/t+A_j x)).

Let t tend to infinity. Continuity of sigma and the finite sums imply

    MAX_N(x)=sum_k v_k sigma(sum_j W_kj sigma(A_j x)).

Thus a bias-free network with precisely the same two widths computes MAX_N.
No approximation argument or additional neuron is involved.

## 2. One diagonal tangent normalizes all inner functions

For the homogeneous network define

    alpha_j=A_j e,
    s_k=sum_j W_kj sigma(alpha_j),
    ell_k(x)=sum_{alpha_j>0} W_kj A_j x,
    q_k(x)=ell_k(x)+sum_{alpha_j=0} W_kj sigma(A_j x).

For a fixed x and all sufficiently small epsilon>0,

    sum_j W_kj sigma(A_j(e+epsilon x))=s_k+epsilon q_k(x).

The directional derivative of sigma at s in direction u is u for s>0,
zero for s<0, and sigma(u) for s=0. Taking the directional derivative of the
network at e, and using MAX_N(e+epsilon x)=1+epsilon MAX_N(x), gives

    MAX_N(x)=sum_{s_k>0} v_k q_k(x)+sum_{s_k=0} v_k sigma(q_k(x)).

Every surviving nonlinear first-layer form has A_j e=0. For a surviving
nonlinear second-layer term, ell_k(e)=s_k=0, so q_k is translation-invariant:
q_k(x+t e)=q_k(x). The first sum is a linear form plus a shallow linear
combination of the surviving first-layer ReLU functions. Its linear part
has value sum_{s_k>0}v_k s_k=1 at e.

We therefore obtain the normalized presentation

    MAX_N(x)=Lx+sum_j B_j sigma(A_jx)+sum_k d_k sigma(g_k(x)),
    g_k(x)=U_kx+sum_j W_kj sigma(A_jx),
    A_j e=U_k e=0,  Le=1.

There are at most h1 first nonlinear forms and at most h2 nonlinear outer
terms. The shallow and linear terms are internal proof expressions, not an
alteration of the original theorem's architecture. Zero coefficients can
retain the original index sets literally if preferred.

## 3. Exact coordinate localization with a diagonal-preserving lift

Let S be any nonempty subset of coordinates. Fix a in S and define H_S from
R^S to R^N by

    (H_S y)_i=y_i if i is in S, and (H_S y)_i=y_a otherwise.

This lift satisfies H_S 1_S=e. Choose q with q_i=0 on S and q_i<0 outside S,
and with A_j q nonzero whenever supp(A_j) is not contained in S. Such q exists:
enumerate the outside coordinates i_1,...,i_r, set q_{i_l}=-t^l, and take t>0
large enough that each of the finitely many nonzero polynomials A_j q is
nonzero. For supports contained in S, A_j q=0 automatically.

For every epsilon>0 and every y,

    MAX_N(q+epsilon H_S y)=epsilon MAX_S(y).

Indeed the selected coordinates are epsilon y_i, while an outside coordinate
is q_i+epsilon y_a<epsilon MAX_S(y). Taking the directional derivative at q
therefore gives an exact normalized representation of MAX_S with no larger
widths.

Here are the full algebraic details of the surviving functions. Put
J_S={j:supp(A_j) subset S}, and write a_j for the restriction A_j|_S when
j is in J_S. For the derivative of the k-th inner function put

    u'_k(y)=U_k H_S y+sum_{A_jq>0} W_kj A_j H_S y,
    g'_k(y)=u'_k(y)+sum_{j in J_S} W_kj sigma(a_j y).

The new nonlinear second-layer terms are exactly d_k sigma(g'_k) for those
k with g_k(q)=0. A term with g_k(q)>0 contributes the shallow/linear function
d_k g'_k, and a term with g_k(q)<0 contributes zero. The original shallow
terms localize by the same scalar rule.

Since H_S 1_S=e, every a_j and every u'_k has zero coordinate sum. The new
output linear form has value one on 1_S; every added linear summand has
zero coordinate sum. Hence translation normalization is already preserved.
In particular, **no additional diagonal localization is needed**.

The surviving nonlinear first forms are precisely the whole-contained rows:
their supports are supp(A_j), now regarded as subsets of S. A row meeting
the complement of S is frozen into a linear expression; it is not replaced
by its coordinate intersection. This distinction is essential for averaging.

## 4. A single elementary averaging bound controls both support costs

Set n=floor(N/2), and choose S uniformly from the n-element subsets of [N].
For a fixed support T of cardinality r,

    P(T subset S)=(n)_r/(N)_r <= 2^(-r)

when r<=n; the probability is zero otherwise. The displayed inequality follows
termwise from (n-i)/(N-i)<=n/N<=1/2.

Let

    B=sup_{r>=3} r^4 2^(-r) < infinity,
    Q(S)=sum_{j:|supp(A_j)|>=3, supp(A_j) subset S} |supp(A_j)|^4.

Then E Q(S)<=B h1. Consequently one S has Q(S)<=B h1. Localize using the
preceding lemma. In the resulting exact normalized MAX_n model, if M is the
number of nonlinear first forms with support at least three and L4 is the
sum of fourth falling support factorials, then simultaneously

    81 M <= Q(S),    L4 <= Q(S) <= B h1.

This uses one and the same S and avoids the optimized joint-cost machinery.
The finiteness of B is elementary: the ratio of successive terms r^4/2^r
tends to 1/2. One may also take B=150 since sum_{r>=0}r^4/2^r=150, but there
is no need to name a numerical value in an existential-constant proof.

If h1<=C N^2 and N>=3, then n>=1 and N<=3n. Thus Q(S)<=9B C n^2. The
support count and fourth moment needed by the counting proof are therefore
both O(C n^2), with absolute implicit constants.

## 5. Finite small dimensions require no extra width theorem

For the paper statement quantified as 'for every C>0 there exists c_C>0',
suppose the counting argument proves h2>=a_C N^2 whenever N>=N0(C), where
a_C>0. An ordinary network with h2=0 is constant, so an exact MAX_N network
has h2>=1. Replacing a_C by min(a_C,1/N0(C)^2) covers all N>=3. This does not
claim the stronger uniform dependence c/max(1,C); that quantitative result
is supplied separately by the explicit Lean theorem.

## Alternative routes and choices

* DIRECT_REPLACE: recession removes all biases in one line and preserves
  the ordinary architecture before subsequent normalization.
* KEEP: the tangent at e has a transparent explicit formula and simultaneously
  normalizes both nonlinear layers.
* DIRECT_REPLACE: a diagonal-preserving lift removes the second normalization
  normally needed after extending selected directions by zero.
* DIRECT_REPLACE: fixed-size subset averaging gives one support fourth-moment
  bound; a joint maximum cost is unnecessary for an existential constant.
* KEEP: exact fixed-size sampling avoids a separate Chernoff estimate or a
  random-size conditioning argument needed by naive Bernoulli selection.
* KEEP: finite polynomial avoidance supplies the needed generic base point
  without a measure-theoretic genericity assumption.
* KEEP: for the fixed-C paper theorem, h2>=1 handles finitely many small N;
  optimized constants and the separate linear width theorem can be omitted.

## Checks against tempting errors

The bias limit uses t>0, so ReLU homogeneity is legitimate. The second tangent
is one-sided; it does not assume differentiability at a zero preactivation.
Each directional identity is exact for small positive steps. The first-row
support is retained only when its entire support lies in S. Signed weights
are never replaced by absolute values or assumed positive. New linear/shallow
terms do not create counted second-layer neurons. Original layers may contain
zero rows, duplicate rows, and zero output coefficients throughout.
