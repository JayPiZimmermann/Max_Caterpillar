# Double wheels, their exact failure, and isolated shifted cuts

25 October 2026. All statements concern the canonical rational top kernels,
with arbitrary root, apex, and edge orientations. No uniform separator or
unrestricted exponential lower bound is proved here.

The leaf-double-wheel map is injective on the symmetric outward-twin span at
five labels, but it is **not injective at seven labels**. An exact two-term
witness also has zero iterated residues on every disjoint positive or mixed
branch wheel tested below. Its remaining poles are shifted-minus cuts, and
two such cuts with different apex labels detect it. This retains a concrete
marked boundary algebra while closing the proposed leaf-wheel injectivity
shortcut.

## Conventions and the local arrangement

Write a=omega_apex and root the nonapex tree at the head. For an edge e let
q_e be the sum on its component away from the root, and let epsilon_e=+1
for sigma(x_child-x_parent), -1 for the opposite orientation. The kernel is

    R_U = (-a)^(N-4) / product_e q_e(q_e+epsilon_e a).

All equalities are rational identities on sum_i omega_i=0. Frequencies are
generic away from the stated pole strata and other denominator hyperplanes.
Residues mean coefficients of s^(-1), with the other displayed coordinates
fixed. Full label sums are unaveraged: every one of the N! permutations is
included, including automorphism multiplicities.

Fix distinct labels a,l,m and put s=omega_a+omega_l,
t=omega_a+omega_m. For N>=5, a unit with actual apex outside {a,l,m} has
zero iterated double residue. A shifted-minus cut cannot vanish identically
on this stratum: its actual-apex coefficient differs from that at another
outside label, whereas every linear combination of s,t has equal outside
coefficients modulo the common-coordinate relation. The remaining ordinary
cuts would have to give the two splits {a,l} and {a,m}. These splits cross
on the nonapex tree, so they cannot both occur.

For an apex in the triple, the localized arrangement is contained in

    s, t, s+t, s-t.

At most two denominator factors of a single kernel vanish there. Indeed,
the apex frequency is nonzero, so at most one factor per edge vanishes;
the apex together with any choice of one shifted or unshifted edge factor
is a basis. Three independent forms cannot lie in this two-dimensional
normal space. Consequently the leading normal degree is at least -2.
The degree -2 simple-fraction space has basis

    b0=1/(st), b+=1/[s(s+t)], b-=1/[s(s-t)].

Swapping l,m fixes b0 and sends b+ to b0-b+, b- to -b0-b-.
Thus a fully symmetric function has only its b0 channel. For these
functions one ordered leaf-double residue captures the complete leading
leaf-double-wheel data; all choices of three labels are conjugate.

## Exact five-label positive control

There are three distinct symmetric outward-twin function orbits. With apex
0, representatives are

    root1: (2,1),(3,2),(4,2);
    root1: (1,2),(3,2),(4,2);
    root2: (2,1),(3,2),(4,2).

Each pair (u,v) means sigma(x_u-x_v). A fourth literal rooted-star orbit
equals the first by a root slide. In the chart

    omega=(a,s-a,t-a,b,a-b-s-t),

the double residues of these full S5 sums are respectively

    -12(a²-ab+b²) / [ab(a-b)(a+b)(2a-b)],
    4(12a⁴-14a³b+13a²b²+2ab³-b⁴)
       / [ab(a-b)(a+b)(2a-b)(2a+b)(3a-b)],
    8 / [ab(a-b)].

They are linearly independent: the unique pole b=-2a first forces the
second coefficient to vanish; b=-a then forces the first; the third is
nonzero. The producer and independent checker use different cut
parameterizations and verify all 120 permutations, including every
outside-apex contribution. The finite denominator classification is also
checked for N=5,...,9. This is a finite positive control, not an induction.

## Exact seven-label counterexample

Let U and V have apex0, root1, and oriented edges

    U: (1,2),(1,3),(1,4),(5,2),(6,2),
    V: (1,2),(1,3),(4,2),(5,2),(6,2).

Both have nonroot outward twins at vertex2. Let

    W = -3 sum_(pi in S7) R_(pi U) + 2 sum_(pi in S7) R_(pi V).

The complete leaf-double-wheel data of W vanish. This is exact: after
restriction, every coefficient of each identical primitive-denominator
fraction cancels. It does not rely on a sampled rank. The independent
checker starts from positive-endpoint components, uses another external
frequency chart, checks all 5040 permutations of each unit, and proves
these cancellations term by term. It also gives the fresh exact value

    W(-33,3,4,5,6,7,8)
      =1023022803722705038478750493973
       /455746540313582618712131520000000 != 0.

This refutes injectivity, not outward-twin separation: in particular it
does not express the maximum using outward-twin units.

The diagnostic producer used the complete 258-orbit six-vertex inventory.
Among its92 literal outward-twin columns, the saved generic modular rank
is47, while the leaf-residue evaluation rank is36. These ranks motivated
the witness; the exact two-term argument above is the actual certificate.

## Branch controls and the remaining poles

For disjoint nonempty S,T and a outside them, write

    H1=omega_a+sum_S omega,
    H2=omega_a+tau sum_T omega, tau in {+1,-1}.

At N7 the two standard iterated residues of W vanish exactly for every
nondegenerate size type with |S|+|T|<=5: all six positive types up to
interchange, and all ten ordered mixed-sign types. Every combined fraction
dictionary is empty. The excluded covering case can force a coordinate
hyperplane and is not included. These statements concern the specified
iterated residues; no unproved completeness claim about the larger local
normal arrangement is made.

The ordinary two-label-cut residue is identically zero term by term.
For the ordinary three-label cut,60 fraction records initially remain;
clearing their common denominator, a product of28 primitive linear forms,
gives the zero polynomial over Q in five variables. By symmetry and
complementation this removes every noncoordinate ordinary-cut pole of W.
The singleton-minus and two-label-minus residues also cancel identically.
Only shifted-minus pole types of sizes3 and4 remain, besides coordinate
poles. Both remaining types are nonzero; this is established by exact
rational evaluations, not inferred from uncancelled fraction records.

In particular, take a,b outside the same set S and use

    H1=omega_a-sum_S omega=s,
    H2=omega_b-sum_S omega=t.

These cross-apex pairs detect W. At the external free coordinates
(1,10,100,1000), the values, equal in both orders, are

    |S|=3: -5512019473/137054472797038500000,
    |S|=4:  3359973/170816357211500000.

The independent checker uses rooted cuts and their signs, rather than
positive-endpoint components, and reproduces both values. The mechanism
is explicit: on H1=0 the singleton-minus factor omega_a-omega_b is -H2.
Cancellation of an ambient diagonal between two apex sectors can therefore
leave a cross-apex double pole. A common-apex branch alphabet misses it.

## Uniform isolation and a marked product recurrence

For 2<=|S|<=N-2, the pole

    H=omega_a-sum_S omega=0

can occur only in the sector whose **actual apex is a**. Ordinary cut forms
have two coefficient levels. A genuine shifted-minus cut has three levels,
with a unique extremal apex coefficient. Since both S and its nonapex
complement are nonempty, equality modulo the common-coordinate relation
and nonzero scaling forces that unique apex to be a. The singleton case
is different: omega_a-omega_b can exchange a and b. Thus every nonsingleton
shifted-minus residue in a mixed-apex rational identity cancels within one
apex sector.

Here is the exact residue at an inward edge. Let C be its child component,
D the root component, v its child endpoint and h its endpoint in D. Put
q=sum_C omega and take the residue at q-a=0. Define two smaller canonical
kernels:

* C: root v, new apex frequency -a, every internal edge orientation reversed,
  and the original frequencies at its vertices;
* D: original root and orientations, apex frequency a, with only the hub
  frequency shifted by omega_h -> omega_h+a.

Then

    Res_(q-a=0) R_U = (-1)^|C| a² R_C R_D.

The frequency sums are correct because sum_C=a and sum_D=-2a. Each cut
inside C is unchanged, while reversing its orientation and the apex sign
leaves q_e(q_e+epsilon_e a) unchanged. A cut in D originally included C
exactly when its reduced child component contains h; the hub shift therefore
reproduces its old q_e. The removed edge contributes1/a. Comparing the two
numerator powers gives precisely (-1)^|C|a². This proof also covers a
singleton component; the kernel numerator then has the corresponding
negative exponent. The independent checker tests all inward edges of U,V,
including singleton components.

For an outward edge, the analogous residue at q+a=0 is a² R_C R_D:
C keeps apex a and all orientations, while D keeps apex a and shifts its
hub by -a. This follows by the same cut comparison.

For the original leaf wheel with its actual apex a, deleting two outward
leaves at a common hub instead gives the lower canonical kernel with that
hub frequency shifted by -2a. Two different hubs receive -a each. These
are marked attachment operations, not a scalar recursion.

An inward-edge split preserves an original outward-twin pair in one of
its two tree components, since that edge cannot be one of the pair's
outward leaf edges. However, the detached component reverses orientations.
Consequently a recursion must retain this state; it cannot silently apply
an outward-twin annihilator to both factors.

The live unresolved presentation problem is whether cancellation of all
isolated shifted-minus cuts admits a controlled reduction to the
all-outward sector while retaining the appropriate twin/attachment ideal.
Neither the residue identities nor the exact finite controls prove this.

## Reproduction and evidence boundary

The `overnight_uniform_doublewheel*.py` producers and independent checkers
have adjacent JSON receipts and logs. The complete frozen manifest lists
every input-independent source and small receipt. The N7 producer also
reads the existing `overnight_lower_matching_rows_7.json` inventory; the
small exact witness checker does not require it or any numerical cache.

The only polynomial backend is FLINT in the ordinary-cut cancellation
check. All other new witness, cross-apex, and product controls use exact
standard-library rational arithmetic. No numerical rank is promoted to a
rational identity, and no exact control here establishes the missing
uniform separator.
