# Verified conditional square-root exponential transfer

The complete normalized theorem, raw affine-skip wrapper, and public-root
exact gate pass. The local structural obstruction H remains an explicit open
hypothesis at the displayed growing orders. The result has growth
exp(c*sqrt(N)), a stretched exponential. It does not establish an
unconditional exponential lower bound, a bound exp(c*N), or quadratic
tightness.

## Exact normalized theorem

Let d>=1 be an integer and n>=10^10*d^2. An actual translation-normalized
homogeneous skip network computes MAX_n with arbitrary real coefficients.
For its ORIGINAL indexed first rows, put

    M = number of rows whose support has at least3 elements,
    L = sum_j (r_j)_4,

where r_j is the support cardinality and (r)_4=r(r-1)(r-2)(r-3). Suppose
M<=d^2*n^2 and L<=d^2*n^2. Define

    q = floor(sqrt(n)/(8000*d)), k0=4q+1.

Under H(k0,q), the verified conclusion is

    h2 >= (1/2)*exp(3*sqrt(n)/(8000*d)).                       (1)

Every sampling, generic-point, support-event, rank, probability, counting and
scalar estimate is derived from the actual arrays and these stated budgets.
The declaration is
`GrowingMatching.Bernoulli.conditional_sqrt_lower_bound`.

H(k,q), formally `LocalMatchingObstruction k q`, says that every actual
normalized braid-first-layer skip network computing MAX_k has an original
second neuron whose summed interaction graph contains q disjoint edges. It
allows arbitrary signed real coefficients and the braid one-layer output.
It contains no width or probability conclusion. Jensen's SC'_(2q-1), at
k=4q+1, implies H(k,q): a maximal matching of size at mostq-1 has endpoints
forming a cover of size at most2q-2, placing the neuron in K_(2q-2), hence in
C_(2q-1).

The needed growing H hierarchy is unproved. The verified H(5,2) instance is a
calibration of its meaning; it is not an instance satisfying the large-n
hypotheses of(1). All growth conclusions here retain the displayed H premise.

## Exact original affine-network theorem

Let C>=1 be an integer. The original affine-skip network may have arbitrary
real first covectors, biases in both layers, and affine skips. Assume it
computes MAX_N on every real input and its TOTAL original first width obeys
h1<=C*N^2. Set

    n=floor(N/2), d=20*C,
    q=floor(sqrt(n)/(160000*C)).

If n>=10^10*(20*C)^2 and H(4q+1,q), then the verified original-width bound is

    h2 >= (1/2)*exp(3*sqrt(floor(N/2))/(160000*C)).             (2)

Normalization and a half-size actual network are constructed internally.
Both hidden widths retain the original index sets. All first slots are
counted, including output-only rows. No braid, support, normalization, rank,
probability or counting premise is supplied by the caller. The declaration is
`GrowingMatching.Bernoulli.Affine.conditional_affine_sqrt_lower_bound_explicit`.
Thus a quadratic first-width budget permits conditional exp(c_C*sqrt(N))
growth for each fixed C, assuming the indicated local structural obstruction.

## Literal sampling parameters

The normalized proof uses

    p = 1/(1000*d*sqrt(n)), mu=n*p=sqrt(n)/(1000*d),
    K = floor(n/(1000*d^2)),
    q = floor(mu/8), k0=4q+1,
    b = floor(2*mu), m0=n-b,
    c0 = 7K/(24*n^2).

Each original coordinate label enters S independently with probability p.
Conditional on S, the tail order and gap ranks are genuine independent uniform
permutations of its complement. Their dimensions vary with S. No uniform
full-permutation law is asserted for this Bernoulli-selected S.

Define the actual downward event

    D0 = {no original first row of support at least3 is wholly in S}
         intersect {|S|<=b}.

The measure is the literal finite product weight

    w(S)=product_i (p if i in S, otherwise1-p).

Its normalization, exact fixed-label inclusion probabilities, modular weight
identity and weighted FKG association are proved. In particular, for any fixed
set I of ORIGINAL labels,

    P(I subset S | D0)<=p^|I|.                               (3)

The same domination holds for every increasing selected-set event, including
the event that a fixed graph contains a selected q-matching.

## Why large enough selected sets remain available

Support avoidance is decreasing, so positive association gives

    P(no internal nonbraid row)
       >= product_j(1-p^r_j) >= exp(-2*M*p^3).

The exact cardinality MGF is (1-p+p*exp(t))^n. Its proved finite exponential
Markov bounds give

    P(|S|>2*mu)<=exp(-mu/3),
    P(|S|<=3*mu/5)<=exp(-3*mu/40).

The literal parameter inequalities imply mu>=100 and k0<=3*mu/5. Hence D0
has positive mass, and the small-arity probability conditional on D0 is at
most

    exp(-3*mu/40) /
      [exp(-2*M*p^3)-exp(-mu/3)] <=1/100.                    (4)

The denominator and its positivity are derived, not assumed in(1). This is
where the rare-event estimate is used. The final per-neuron matching bound
below has no loss of a factor1/P(D0).

## Conditional good-event budget

The role spaces consist of four distinct ORIGINAL support labels. Their
cardinalities are (r)_4/4, (r)_4/2 and (r)_4/4 for cases A,B,C. Fixed-S tail
placements are actual inverse-permutation events. Their uniform laws are
proved even if a proposed label tuple fails to lie in the tail, when its
event is empty.

For A, drop tail-membership restrictions when taking the conditional S
expectation. For B retain its one specified selected label; for C retain its
specified pair of selected labels. Equation(3) gives factors p and p^2.
Thus the literal original-row support-good failure probability conditional
on D0 is at most

    L*K^2 / [(1-K/m0)*(m0)_4]
    + L*p*K^2 / [m0*(1-K/m0)*(m0)_3]
    + L*p^2*K / [2*(m0)_2].                                (5)

No independence of overlapping adjacent-pair/run events is used. Their
adjacent-pair count is bounded pointwise before taking run expectations.
All three selected-arity terms are retained.

For the stated parameters and L budget, (5)<=1/1000. The short-isolated-gap
failure probability is at most8K/m0<=16/1000. Together with(4), at least9/10
of the conditional sample remains available for the actual witness argument.

## Actual survival and selected-matching cost

One sufficiently large actual gap scale works simultaneously for every S,
every tail/rank permutation, and every original row and second neuron. This
threshold is derived from the original real arrays. The point, zero tests,
activation masks and original neuron indices agree throughout the proof.

On a fixed recorded matching-data fiber, genuine local swaps provide fair
comparison coins. Joint actual cleanliness and second-neuron survival are
bounded by the actual matching moment. Cleanliness is discarded after this
conditional rank bound. The proof never replaces this with survival
conditional on Good.

Let eta be the ordinary edge count of one original neuron's actual ambient
braid graph. The moment at a long isolated matching obeys

    E_tail[2^(-X)]<=exp(-7*J*tR/[12*m*(m-1)]), J>=K/2.

First weaken this rate to c0 while the actual tail edge count tR is
nonnegative. Only then substitute

    tR>=eta-b*(n-1).

The deletion lower bound can be negative; this order of inequalities is
necessary. The same ambient graph and selected labels are used on both sides.

A q-matching has2q distinct endpoints and at most eta^q/q! possible edge
sets. Its increasing selected-set event is dominated under D0 by its
unconditioned Bernoulli probability. Consequently the conditional per-neuron
cost is at most

    p^(2q)*eta^q/q! * exp[-c0*eta+c0*b*(n-1)].

The factorial is retained until the exponential-series inequality

    exp(c0*eta)>=(c0*eta)^q/q!

cancels eta^q/q!. This yields the derived actual-event bound

    [p^2/c0]^q * exp[c0*b*(n-1)] <= exp(-3*mu/8).             (6)

Selected/tail graph independence is not assumed. This bound uses the joint
clean/survival event and the genuine conditioned selected-set law.

## Actual structural witness and width

On D0, internal first rows are braid rows or zero. When |S|>=k0, the local
structural input applies: H is proved upward-monotone in input arity by
actual further localization and ambient matching transport. It uses no graph
contraction.

Outside the short-gap and support-bad events, H supplies an ORIGINAL second
neuron that vanishes at the same actual point and has a q-matching on S.
The actual raw configurations are therefore covered by the finite union of
these original-neuron events. Averaging this cover gives at least9/10
conditional coverage. With(6), it implies(1), including the verified
prefactor1/2.

For(2), the verified actual half restriction supplies

    4*fourthMoment<=81*h1, 4*M<=h1,
    L<=fourthMoment.

The original quadratic first-width cap and d=20*C give both required d^2*n^2
budgets. The same original second-neuron indices remain throughout.

## Scope and evidence

Whole normalized and raw-affine receipts pass independent expanded statement,
structural-H, literal parameter and ordinary-axiom checks. The accepted axiom
sets contain only propext, Classical.choice and Quot.sound. The exact gates
record the full source closures and check source stability.

The headline receipts are `bernoulli_lower_bound_receipt.json` and
`affine_bernoulli_receipt.json`. The actual sampling, association, MGF,
conditioned good-event, survival, graph-count and scalar components also have
separate scoped receipts. Finite exploratory controls are not used as proofs.

The fixed-size union-bound n^(1/3) restriction was a limitation of that
argument. Downward Bernoulli conditioning proves the stronger conditional
square-root regime. The growing H obstruction remains the unproved step;
no claim here establishes a true exp(c*N) bound or an upper bound showing
quadratic tightness.
