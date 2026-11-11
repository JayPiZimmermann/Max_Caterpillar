# A logarithmic counterexample to the raw cubic transfer cost

**Mathematical result:** the proposed uniform actual-neuron estimate

    P(survives ∩ local G outside C₂ ∩ Good_K ∩ |Q_K|≥K/2) ≤ C/K³

is false for the **uniform seven-set / independent uniform tail and rank permutation law**, even for a family with O(N) first rows, all supports at most four. For K=floor(δ(N−7)), any fixed 0<δ≤1/256, the constructed event has probability

    [210 α(1−α)^4 + o(1)] log(N)/N³

when |P|/N→α∈(0,1). This is an actual-preactivation counterexample to a raw cost estimate, not a network computing MAX, not a counterexample to a superquadratic NETWORK lower bound, and not a claim about the score of any particular SC′₂ certificate. The all-N argument below is mathematical; finite exact controls and two independent audits support it. It has not been formalized in Lean.

## 1. Original real network, before localization

Choose distinct input labels a,b,z,t and a set P disjoint from them, |P|=r. All coefficients below are integers. Let

    h(x)= Σ_{e≠a,b} [σ(x_e−x_a)+2σ(x_e−x_b)]
          + Σ_{c∈P} σ(x_c−x_a+x_z−x_t) − σ(x_z−x_t).

There are `2(N−2)+r+1=2N−3+r` first rows. The core and final row have support two. Each of the r guard rows has support four. Every row is zero-sum; no unspecified linear skip or affine bias is used. Thus M=r and the fourth-support sum of the nonbraid rows is exactly 24r. In particular this does not need a quadratic budget of large-support rows.

This is one genuine second preactivation. The outer output can be σ(h). We do not assume it computes MAX_N or that it is an indispensable unit of a minimal MAX network. The uniform per-neuron cost route under audit was intended to hold independently of those additional global conditions. A cost estimate exploiting minimality or global crease cancellation would be a different possible route.

## 2. Selected sets and the exact rank event

Use a uniformly random seven-set S and independent uniform permutations of its m=N−7 tail labels and its m gap ranks. Ranks are 0,...,m−1; Γ_K is the set of gaps with rank <K. Human tail positions are 1,...,m; human gap 1 lies between the selected anchor block and the first tail coordinate. This is gap index 0 in the Lean definitions.

Impose the selected-set event

    a,b∈S, z,t∉S, |P∩S|=1.

Write c* for its unique selected P label. Its probability is exactly

    s_N = r choose(N−r−4,4) / choose(N,7).

Conditional on the selected-set event, z,t occupy a uniform ordered pair of distinct tail positions among 1,...,m. Require z at position s and t at position s+d with s≥1 and d≥2. For each d∈{2,...,m−1}, there are m−d such oriented placements. No extra orientation factor is needed. The first tail label is unrestricted: all tail coordinates are at most −γ₁, regardless of its label.

Let H be the rank of human gap 1. Require

    H≥K,
    H> every rank of the d intervening gaps s+1,...,s+d.

The first inequality is deliberately ≥K: with zero-based ranks, it is exactly enough to exclude the anchor gap from Γ_K. A condition H>K instead would replace K by K+1 in the formulas below.

## 3. Exact survival and actual local function

For any T≥2 define the actual ordered gap point by γ_j=T^(rank_j) and q_(τ_i)=−Σ_{j≤i}γ_j, with q_S=0. Let

    v=q_z−q_t=Σ_{j=s+1}^{s+d}γ_j.

All d ranks in this sum are below H and are distinct, so

    0<v≤Σ_{j=0}^{H−1}T^j<T^H=γ_1.

Every tail coordinate is at most −γ_1. Hence:

* all external core rows x_e−x_a and x_e−x_b are negative at q;
* the c* guard has value v>0;
* every tail-c guard has value q_c+v<0;
* the final row x_z−x_t has value v>0.

Every noninternal first row is therefore nonzero at q, every nonbraid row is external because z,t∉S, and the actual active-gate gradient is

    V=(e_c*−e_a+e_z−e_t)−(e_z−e_t)=e_c*−e_a.

Thus every tail coefficient, every tail-subset sum and every prefix sum is zero. Directly h(q)=v−v=0: this is actual survival, not an assumed local characterization. The argument works for every sufficiently large common generic gap scale, since it already works for every T≥2.

The active external rows keep their signs in a neighborhood of q. Restricting perturbations to S gives the actual local preactivation

    h_local(y)=Σ_{e∈S\{a,b}}[σ(y_e−y_a)+2σ(y_e−y_b)]+y_c*−y_a.

Its Boolean quadratic is

    G(B)=Σ_{e∈S\{a,b}}1_e[(1−1_a)+2(1−1_b)]+1_c*−1_a.

G(empty)=G(S)=0. Its interaction graph is exactly K_{2,5}, with all hub-leaf coefficients nonzero. Its only vertex cover of size at most two is {a,b}. Every anchor must be a vertex cover (the elementary quadratic second-difference identity), whereas G({a,b})=−1. Consequently it has no anchor of size at most two and its graph has vertex cover two, so it lies outside C₂.

It also has a nonzero individual top Boolean interaction:

    μ_[7](G_+)=1.

See the complete identity and exact finite checks in README.md and sharp_cubic_control.py. This does not identify the value of a particular certificate Φ(G), and does not make the single unit glue.

## 4. Literal Good_K correspondence

Here Good_K means the complement of the actual support-role family event in `GrowingMatching/Bernoulli/GoodEvent/Events.lean`, evaluated for the uniform fixed-size-seven selection law. Its role placements are precisely the original-label cases A, B and C. They do not depend on the numerical row weights.

All support-two rows have no four-distinct-label role. Consider a guard support {a,c,z,t}.

* If c∉S, its only selected label is a. Case A is impossible because it has only three tail labels, and C is impossible because it has only one selected label. Only B could remain, but B needs a tail support label in the anchor Γ_K-run. Human gap 1 is absent from Γ_K, so that anchor run contains no tail position at all.
* If c=c*∈S, the only tail support labels are z,t. A and B need more tail labels and are impossible. C would require z,t to be adjacent with their gap in Γ_K. Their distance d≥2 rules out adjacency.

Therefore the literal family bad event is absent. This proves Good_K itself, not merely absence of an actual nonbraid-dominant cherry.

## 5. Exact probability and the logarithm

For a fixed distance d, the distinguished rank H is the maximum among these d+1 distinct gaps with probability 1/(d+1). Their unordered rank set is uniform. The probability that all their ranks are below K is `(K)_(d+1)/(m)_(d+1)`. Thus the exact rank-event probability is

    p_d = [1−(K)_(d+1)/(m)_(d+1)]/(d+1).

The falling factorial in the numerator is zero if K<d+1. The event before imposing EnoughCherries has exactly probability

    s_N · b_(m,K),

where

    b_(m,K)= 1/[m(m−1)]
      Σ_(d=2)^(m−1) (m−d)/(d+1)
        [1−(K)_(d+1)/(m)_(d+1)].

The uncorrected sum is exactly

    (m+1) H_m − (5m−1)/2.

For K≤δm with fixed δ<1, the removed sum is O_δ(m), since the falling-factorial ratio is at most δ^(d+1) and Σ_{d≥2}δ^(d+1)/(d+1) converges. Therefore

    b_(m,K) ~ log(m)/m.

For r/N→α∈(0,1),

    s_N ~ 210α(1−α)^4/N²,

This gives the stated exact leading asymptotic coefficient 210α(1−α)^4. Its maximum over α is at α=1/5, giving 10752/625=17.2032 before the logarithm.

## 6. Retaining the actual EnoughCherries predicate

Let Q_K be `isolatedGaps Γ_K`, whose definition excludes the anchor gap and includes an isolated final gap. Let ν count adjacent pairs of gap indices both in Γ_K. The elementary path bound gives

    |Q_K|≥K−1−2ν.

If |Q_K|<K/2 and K≥4, then ν>K/4−1/2≥K/8. The selected-adjacency path therefore has a matching of at least K/16 edges. For K≥32 put u=floor(K/16), so u≥K/32. A fixed matching of u edges has 2u distinct endpoints, whose probability of all lying in the uniform K-subset Γ_K is at most (K/m)^(2u). There are at most choose(m,u) such matchings. Consequently, for K≤δm,

    P(|Q_K|<K/2)≤choose(m,u)(K/m)^(2u)
                   ≤(32eδ)^u≤2^(−u)

when δ≤1/256. This is an exponentially small bound for K=floor(δm), with fixed δ>0.

The rank witness and Q_K need not be independent. Conditional on the selected-set event, subtract this failure probability inside the remaining rank/position experiment:

    P(all constructed conditions and EnoughCherries)
      ≥s_N [b_(m,K)−2^(−floor(K/16))].

This is a correct finite lower bound; K≥32 alone does not guarantee its bracket is positive. For the claimed asymptotic, the exponential term is o(log(m)/m), so the leading coefficient is unchanged. Alternatively K≥64log₂m makes that term at most m⁻².

Thus K³ times the joint raw survival/non-C₂/Good/EnoughCherries probability grows as a positive multiple of log N. No finite universal C can bound it by C/K³.

## 7. An independently checked restricted event

The first version additionally required the first tail label to lie in P and restricted the z position to s≥2. That restriction is unnecessary for survival or Good, but remains a valid smaller event. Its exact mass is

    s_N (r−1)/m /[(m−1)(m−2)]
      Σ_(d=2)^(m−2) (m−d−1)/(d+1)
         [1−(K)_(d+1)/(m)_(d+1)].

Its leading coefficient is 210α²(1−α)^4. Both the original restricted count and the simpler enlarged count are checked by selector_control.py; the independent probability audit records the initial formula and its enlarged-event addendum.

## 8. Evidence, independent audits and limitations

* `selector_control.py/.json`: exact integer original ReLU and active-gradient checks, all tail-subset equations, all 128 Boolean localizations at a rational neighborhood input scale, literal role Good and actual isolated Q. Full tail/rank enumeration is used for the fixed selected-set controls N=11,12. The observed raw counts agree exactly with the independent closed probability formula.
* `selector_probability_check.py/.json` and `selector_probability_audit.md`: independent probability audit, including 115 complete rank-permutation cases, 131071 isolated-gap subsets and 72 selected-set counts. It flags the finite-size bracket qualification explicitly.
* `independent_audit_roles.md`: independent correspondence to the original-label role events and gap indexing.
* `AdaptiveOffset.lean`: separate kernel-verified nine-input counterexample to freezing the offset from all-prefix vanishing. This is not a Lean formalization of the present logarithmic asymptotic.

All of these are isolated research artifacts. No SC′₂ certificate is assumed verified. No new bound for an exact MAX network follows. The result closes one proposed shortcut: a raw constant cubic cost is false. A score-sensitive bound, a logarithmic-cost upper bound, or a theorem using indispensability/global crease cancellation remains possible. This result also does not apply automatically to the variable-arity Bernoulli sample law developed elsewhere in the project.
