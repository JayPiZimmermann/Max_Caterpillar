# Independent audit of the generating-function lower bounds

**Verdict:** the uniform improvements in `lower_count_elegance_routes.md`
are valid. This audit is mathematical; it is not a Lean certificate.
The finite controls in `lower_count_elegance_check.py` support the
derivation but are not the reason the all-N statements hold.

## The cross-size injection

Fix one unit-inner-weight forest and its values kappa. A deleted pendant
has degree one and kappa=0. It and its neighbor have the same tied status:
if the pendant alone were tied, activity would fail; if its neighbor alone
were tied, outside balance would demand kappa=1 at the pendant. If both
endpoints are deleted pendants, the whole component must be tied, since
otherwise its lower endpoint has one higher neighbor. An original isolate
is tied exactly when kappa is nonzero. All other labels are in Phi.

These statements determine the entire tied set from A=T intersect Phi,
without referring to its cardinality. In particular the injection is
valid across all tied sizes. For 0<y<=1, y^|T|<=y^|A|. Therefore summing
over all passed tied sets before taking a block bound is legitimate.
This removes the old loss from treating each size separately.

For each fixed T, balance fixes the outdegrees in F-T after subtracting
the contribution of tied neighbors. A forest orientation is determined
by these outdegrees. Hence every passing order satisfies one prescribed
orientation on each chosen subblock. Relative orders on disjoint sets of
outside vertices are independent under the uniform outside permutation.
Ignoring edges between blocks only enlarges the set of admissible orders.

## Exact blocks

The edge factor is E(y)=1/2+2y+y^2. For a three-vertex path, the empty
selection has order probability at most1/3: its prescribed orientation
has at most two linear extensions among six orders. If only the center
is tied, there is no order restriction; if only a leaf is tied, the
remaining edge has probability1/2. Thus the coefficient of y is2, and
the complete factor is P(y)=1/3+2y+3y^2+y^3.

A reduced isolated vertex with a pendant uses a distinct pendant edge,
giving1/2+y. A forced tied singleton gives y. The selected pendants are
outside Phi and cannot collide with other blocks. A degree-two forest
can be partitioned into edges and three-vertex paths, apart from these
singletons. The covering-subforest version for source-oriented full
tree functions has the same disjointness and factorization.

Consequently

    F_U(y)=sum_T a_U(T)y^|T|
        <= product over blocks of their factors,

where a_U(T) is the fraction of outside orders passed by U. At each
T of size at least3 the common local test gives sum_U a_U(T)>=1.
Multiplying by y^|T| and summing proves the global covering inequality.

## Improved pure-base rate

At y0=sqrt(3/2)-1,

    E(y0)=1,
    P(y0)=1/3+(1/2)sqrt(3/2)=5/6+y0/2<1,
    1/2+y0<1,  y0<1.

Thus F_U(y0)<=1 and

    |K| >= (3/2)^(N/2)-1-N*y0-binomial(N,2)*y0^2.

The subtraction is exactly the omitted tied sizes0,1,2. If all canonical
oriented star face functions are free, detection starts at size5, so
subtract the binomial terms through degree4 instead. The exponential
rate is unaffected. The same argument at y=1/6 also removes the
polynomial loss while retaining the old7/6 base.

The removal of the polynomial loss applies to every reduced-degree
bound Delta, not only Delta=2. At the existing y=1/(2*Delta+2), the old
star factors are already at most one; the exact orientation factors
are no larger. Thus the bound is(1+y)^N minus the same quadratic
truncation. More generally any0<y<=1 for which every star factor
W_s^*(y),1<=s<=Delta, is at most one gives this conclusion. The radical
choice above is the explicit improvement for Delta=2.

## Original N in the Bernoulli mixtures

At y=1/2 put tau=sqrt(7)/2>1. The factors satisfy

    1/2+y=1<=tau,   y<=tau,
    E(y)=7/4=tau^2,
    P(y)=53/24<=tau^3,

the last inequality being2809<=3087 after squaring. Therefore

    F_U(1/2)<=tau^|Phi|<=tau^N.

The second inequality is the key original-N check: its direction uses
tau>1. Extra pendants, original isolates, and two-pendant components
were already accounted for by the cross-size injection and
y^|T|<=y^|A|. There is no replacement of original N by the reduced size.

Multiplying by(2/3)^N normalizes to Bernoulli selection with p=1/3,
giving base capacity at most(7/9)^(N/2). A matching of size at least k
in an added weighted pseudoforest gives independent component witnesses
of probability2/9. Its capacity is at most

    (7/9)^k [1+2k/7+4*binomial(k,2)/49].

Since2k<=N, the base capacity is no larger than(7/9)^k. The common
covering inequality therefore yields

    Z >= Pr(Binomial(N,1/3)>=r)
         (9/7)^k / [1+2k/7+4*binomial(k,2)/49],

with r=3 normally and r=5 for free canonical stars. The stated lower
prefactor1/2 is valid at N=9,r=3 and N=15,r=5 and then for all larger
N by Bernoulli coupling. The exact threshold checks in the companion
receipt are12259/19683 and8551019/14348907, respectively.

The p=1/4 version with13/16 follows in the same way and is valid, but
the exact three-vertex order probability permits the sharper9/7 base.
Excess at most b changes the matching lower-tail polynomial to the
sum through degree b+2; it does not change the base-block argument.

## Head scope and remaining restrictions

The generic ordered-tie stratum with tied height1 is valid for arbitrary
real heads. On that stratum a preactivation is affine in the free outside
coordinates. Avoiding all proper zero sets in the finite expansion makes
any surviving preactivation identically zero on the stratum. This kills
both its outside coefficients and the coefficient of common tied shift.
Consequently the same balance and isolated-label conditions follow
without base-B arithmetic or head integrality. Height0 would not force
that constant coefficient to vanish.

Unit inner coefficients remain essential to the pendant and balance
rules used here. Added weighted pseudoforests use a different necessary
condition, supplied by the same germ. The result still does not prove
an exponential bound for unrestricted orientations of arbitrary trees.
Arbitrary weighted or arbitrary-head stars are not covered by the free
canonical-star separator. Source-oriented added tree functions are full
units; their arbitrary face states are not automatically included.
