# Independent audit of the exact-three-shared necessary models

Status: 31 October 2026. **The corrected necessary-model bridge passes this
audit**, including the optional rigid-contact clauses. This is not an
unsatisfiability certificate, a construction, or a complete exclusion of
the three-shared-contact case. No Lean files were changed.

Audited producer:
`research/sN/frontier5/max5_exact_three_shared_local.py`, SHA256
`e9ea5d767546ea8f5fb06a661ff962d7cb4034f5eea0a370353f45364d66072e`.
This extends the earlier audit of source
`634ac5e726cb6f6e713284aa165294003e1593fd32aaa90a4a6ade4d137cd3e5`
to the optional coefficient gauge and known-support simplifications.
The source also has an optional prescribed-support argument.
The correctness of restriction to one prescribed support multiset is
included here; completeness of a separately supplied support list is not.

## 1. A real implementation error was found and corrected

The initial implementation used `row[k]/2` in the midpoint-gradient
formula. The mandatory root rows are Z3 integer expressions, because their
two orientations were built with integer-valued `If` expressions. Thus
this syntax generated integer division for those rows. For example,
positive one divided by two became zero instead of one half. It was not
a valid encoding of the intended local gradient.

The producer now uses `z.RealVal('1/2')*row[k]`. Both this audit and the
two-unique-contact analysis identified the sort problem. Earlier emitted
SMT files must not be used as necessary models unless regenerated with
the correction. The parent reported only UNKNOWN results from the
affected initial runs; no refutation depends on them.

The independent control script
`research/sN/frontier5/max5_three_shared_model_check.py` now traverses the
actual Z3 expression trees of all three general models with every optional
local-germ and rigid-contact block enabled. It checks that none contains
integer division. Its JSON receipt binds the producer hash above.

## 2. The three contact cases are a complete discrete cover

Write the residual identity as

```
Max5 = ell + R + ReLU(g) + ReLU(h),
```

where R, g and h belong to the actual span of seven invariant physical
first hidden layer features. Exactly three shared contacts leave two
unique contacts. Up to exchanging the cores, their distribution is 1+1
or 2+0.

For 1+1, label g's unique contact q0, h's unique contact q1, and the
shared contacts q2,q3,q4. A matching at q0 is determined by the shared
label paired with 1; a matching at q1 is determined by the shared label
paired with 0. The nine ordered matching pairs form two orbits under
permutations of 2,3,4 and simultaneous exchange of 0 with 1 and g with h:

* The same shared label: g has 12 and 34; h has 02 and 34. Orbit size 3.
* Different shared labels: g has 12 and 34; h has 03 and 24. Orbit size 6.

For 2+0, label g's unique contacts q0,q1. Its consolidated root
curvatures on all edges avoiding both labels must agree in the two
local germs. This forces the same shared edge at the two contacts.
After relabeling 2,3,4, the matchings are 12 and 34 at q0, and 02 and
34 at q1. The common nonzero coefficient fixes their relative signs.

The independent finite checker verifies all nine matching pairs, the
two orbit sizes 3 and 6, and the six signed compatible matching pairs
for 2+0: three choices and two common signs.

At a unique contact, the established one-core Max4 theorem makes the
sole effective core's germ a complementary-pair-max difference with
absolute coefficient one. Complementing a core is legitimate:
`ReLU(g)=g+ReLU(-g)`. Replace g by -g and R by R+g. This retains the
actual feature span, keeps the outer sign positive, and preserves all
zero versus nonzero contact distinctions. The other core's strict sign
can change, so its activity remains a free Boolean variable in the model.
The producer fixes the three representative sign choices by precisely
this operation. It never reverses a physical first feature for free.

## 3. Physical rows and normalization retain the relevant boundaries

One physical row is selected for each mandatory root hyperplane and
positively rescaled to one of its two unit root orientations. Remaining
rows are arbitrary nonzero real zero-sum normals. Their first nonzero
coordinate is normalized to either +1 or -1 by positive scaling, with
the inverse change made to all three coefficient lists. This is a valid
normalization even when either or both core coefficients vanish.

Excluding a zero physical row uses the previously proved first hidden
layer lower bound nine: a zero first feature in the physical (9,4)
network can be pruned, contradicting that bound. The model does not
exclude a zero coefficient, a remainder-only row, linear dependence,
an additional root, or proportional/opposite rows. It even permits
some redundancies already known to be impossible; that only enlarges
the necessary solution set.

The separate `distinct_nonroot` mode deliberately requires every
additional row to have at least three nonzero coordinates and requires
different additional rows to be nonproportional. This is a conditional
subcase. It is not a replacement for the general model.

The optional `coefficient_gauge` instead normalizes the first nonzero
entry in the ordered triple (g coefficient, h coefficient, R coefficient)
to +1 or -1. If its original value is c, multiply the row by abs(c) and
divide all three coefficients by abs(c). Each of the three represented
functions is unchanged. The disjunction explicitly includes g=0 and
h=0 with a nonzero R coefficient, so remainder-only features are retained.
A row unused by all three coefficient lists can be omitted from the
residual representation and hence from a physical realization, contradicting
the established first-width lower bound nine. Its exclusion is therefore
legitimate. The row itself is still required to be nonzero.

The two gauges are alternatives, never simultaneous constraints on a
general row. Mandatory roots always retain their unit root normalization.
Additional rows with a prescribed support of size two also retain the
coordinate gauge, making their two nonzero coordinates +1 and -1. This
justifies replacing their L1 length by the constant two. When no support
is prescribed, an additional row may happen to be a root but its L1
length is still computed from its actual coordinates, as required under
the coefficient gauge.

When a support multiset is supplied, the producer removes one occurrence
of every mandatory root support, assigns the other occurrences to the
remaining physical slots, sets outside coordinates to literal zero,
and makes inside coordinates nonzero. This is exact for that multiset.
Repeats are retained because only one occurrence is removed at each step.
The subsequent Z3 simplification is equivalence-preserving. A theorem
based on many such restricted models must additionally audit the coverage
of the supplied support multisets.

The new support-based shortcuts are also exact: nonzero proportional rows
must have identical exact supports, and two zero-sum rows with the same
two-coordinate support are necessarily proportional. Thus the producer
may replace those parallelism tests by false and true respectively. It
still checks the minors for distinct rows with the same larger support.
For an exact known support, being parallel to a given coordinate root
is equivalent to equality with that root's two-coordinate support.

## 4. Consolidated curvature and the linear part

For a nonzero row a_j, define its L1 length n_j as the sum of its absolute
coordinates. The producer identifies proportional rows using all two by
two minors. For coefficient vector c, it uses the consolidated quantity

```
C_j = sum over k parallel to j of c_k*n_k.
```

This is the correct curvature coordinate. If a_k=t*a_j, its contribution
to the absolute-value part is c_k*abs(t)*abs(a_j.x)/2. Since
`n_k=abs(t)*n_j`, the total absolute-value coefficient is C_j/n_j.
Opposite orientations therefore contribute the same positive normal
length to curvature, with the original signed scalar coefficient.

At q_i=-e_i, rows with negative i-th coordinate are strictly active,
positive i-th coordinate strictly inactive, and zero i-th coordinate
singular. The homogeneous local germ of a shallow core is exactly

```
sum over active rows c_j*(a_j.v)
 + sum over singular rows c_j*ReLU(a_j.v).
```

Its midpoint linear gradient is consequently the sum of c_j*a_j over
active rows plus half that vector over singular rows. This retains the
linear contribution of an opposite pair even when its curvature cancels.
Matching this gradient and each consolidated singular curvature is
equivalent to matching the entire shallow homogeneous germ.

The target comparator `max(pos pair)-max(neg pair)` has midpoint gradient
half the sum of its positive coordinate covectors minus half the sum of
its negative ones. Its root curvatures are +1 and -1. Unit roots have
L1 length two, explaining the producer's curvature right sides +2 and -2.
The complementary shallow pair maximum has curvature +2 on its one root
and midpoint gradient half the sum of its two coordinate covectors.

The root-parallel predicate is valid because each row is already nonzero
and zero-sum: vanishing outside a chosen pair is equivalent to being
proportional to that pair's coordinate difference. The mandatory rows
ensure that every required target ridge is physically present.

These statements remain true with arbitrary dependencies between distinct
planes. A ridge on one full hyperplane cannot be canceled by finitely many
different hyperplanes; cancellation is exactly within proportional groups.

## 5. Shared values, samples, support conditions, and wall constraints

The values at q_i are evaluated by `sum c_j*ReLU(-a_ji)`. Thus shared
conditions impose exactly g=h=0. At a unique contact, the other core is
strictly positive or negative according to its free activity Boolean.

Global Boolean or ternary equations are direct necessary evaluations of
the complete residual identity. They do not claim to identify a global
function from finite observations. The optional shared-contact equations
use the exact directional derivatives just described, retaining a ReLU
for a singular first row. Both outer core values are zero there, so their
directional derivatives pass through their outer ReLUs. The target
derivative is the maximum of the four tied coordinates. Every such
equation is therefore necessary.

The C3 and C4 blocks reproduce the established first-layer support
conditions: every three-label subset contains a first support, and every
label of every four-label subset is covered by a first support within
that subset. They count actual physical rows and do not presume roots.

The imported nonroot-wall condition is guarded by nonzero **consolidated**
curvature in both cores. This is necessary when opposite rows can cancel.
Under that guard, the established wall-collapse theorem reduces the
restriction to one positive outer core, including zero plateaus. The
complete invariant-hyperplane theorem then gives, for every strict
full-support two-versus-three sign pattern, the condition that the largest
absolute coefficient on the three-label side is at least the largest on
the two-label side. The code tests exactly all twenty such patterns and
uses a non-strict inequality, retaining the equality boundary. It imposes
nothing on a core with zero consolidated curvature or on other support
and sign types.

## 6. The optional rigid-contact clauses are necessary

The predicate `good(i)` is a sufficient rigidity condition: at most three
physical rows singular at q_i, or every singular row a root. Counting
physical rows rather than distinct planes can miss some rigid cases, but
cannot falsely declare a case rigid. The applicable local Max4 theorems
allow arbitrary linear terms and provide canonical preactivation germs
for every genuinely nonshallow folded core.

For 1+1, a new canonical germ of a given core at shared q_i must retain
the old matching edge avoiding both its unique contact and i. That
common edge fixes its sign and absolute scale one. The other matching
edge replaces i by the old omitted label. These are exactly the
`shared_pos` and `shared_neg` formulas in the producer. Every good shared
contact must satisfy at least one of the two resulting comparator
conditions. A core already canonical at its unique contact can be
canonical at at most one additional shared contact, by the audited
eight-row bound for three genuine canonical germs. The pairwise
prohibitions implement precisely this restriction, even at contacts
which happen to be canonical without being declared good.

For 2+0, g already has two canonical germs. It cannot supply a third.
At any good shared contact h must therefore be the sole effective
canonical fold, with absolute scale one. The code includes all three
matchings and both signs. It forbids h from being canonical at all
three shared contacts, again by the eight-row bound. No condition is
imposed on a noncanonical shallow folded germ merely because its
preactivation vanishes.

## 7. Independent controls and limits of this audit

The exact rational checker reports:

* 2,500 local directional-derivative reconstruction identities;
* 700 consolidated-curvature identities, explicitly including positive
  proportional rows and opposite rows;
* 700 positive row-rescaling controls;
* 248 coefficient-gauge controls, divided into 200 with g first nonzero,
  40 with h first nonzero, and eight remainder-only cases;
* the complete discrete matching cover described above;
* zero integer-division nodes in twelve actual generated Z3 models: the
  three contact cases, both gauges, and both unrestricted and prescribed
  support forms, with Boolean data, shared local germs, walls, and rigid
  clauses enabled;
* 1,250 exact odd-vector sign-pattern evaluations for the independently
  audited [odd-normal extension](three_shared_odd_import_audit.md).

The JSON status is `FINITE_CONTROLS_PASS_NOT_UNSAT`. The algebraic
arguments above establish necessity; the finite controls catch encoding
errors and independently verify the small combinatorial cover. Solver
refutations still require their own source hashes, trust-free proof
artifacts, and independent proof replay. SAT supplies only local or
finite-data candidates, and UNKNOWN proves nothing. In particular this
audit does not establish the global Max5 minimum.
