LIVE STATUS (2026-10-24): the unrestricted exponential lower bound and an
exponential upper construction remain OPEN. See [the current DFS ledger](all_tree_dfs/CURRENT.md)
and [the independent review](all_tree_review.md) before using historical conclusions below.

Lean verifies the quadratic bound for arbitrary tree units and the exponential
bound for forests of bounded reduced degree, including the Brunck et al.
vocabulary with all units counted. A new exact five-label complete-flag
certificate, together with the canonical-head reduction, gives the mathematical
cubic bound C(N,5) <= floor((N-3)^2/4)|K|; this is not yet formalized in Lean.
Canonical twin separation is certified at five and six labels and measured
modulo a prime at seven. Uniform separation is the remaining lower-bound lemma.

Corrections to older experiments: connected top germs have canonical root heads,
so arbitrary large-head tests do not refute their separation. The stronger
canonical path-separation claim is true at five labels but is refuted at six
by an exact complete-flag identity. Bounded-grid tests do not prove that no
finite uniform mixed-difference functional exists.

# Tree units: does the exponential lower bound survive? (research/sN/trees)

Question: expansions max_N = sum_k d_k U_k + (aux span) where U_k are face functions of
pyramids conv(0, e_r - e_a + sum_{tree edges} [0, g_e]) over ARBITRARY spanning trees of the
non-apex labels (class G of dfs/h4-trees/treeclass.py). Is |K| exponential in N?

## Step log

### 1. Germ reduction at an m-tie (proved on paper, standard; see NOTE.md E1/E2)
At a locality (T, rho) (|T| = m, T tied at the top, others generic below in order rho) every
unit with A(p) != 0 is linear or zero; units with A(p) = 0 (condition (a)) have germ
    G(a, v, F)(z) = relu(<v, z_T> + sum_{(i,j) in M(T)} relu(z_i - z_j)),
with a in T the apex (v_a = -1), F = M(T) a forest on T \ {a}, sum v = 0.
Hence for every (T, rho): sum_k d_k G_k = max_T  (mod linear + span relu(z_i - z_j), i,j in T).
NEW IDEA: use any linear functional on germs that kills a subspace W_m of germ types, not only
"passes / does not pass". If max_m is not in W_m, some unit has a germ outside W_m at every (T, rho).

### 2. Flag invariants (proved on paper, this step)
tau(G) = tau(F_u G) - tau(F_{-u} G) recursively along a flag u_1..u_{m-2}, final stage = lattice
length. Linear in support functions, kills every polytope of dimension < m-1 (lineality argument).
Consequence: only TOP germs count: T \ {a} must be the vertex set of a subtree of the hinge forest.
For coordinate flags this gives back the locality tests; for stars it is still quadratic.

### 3. Path-necessity test PN_m (measured)
PN_m: max_m is NOT in span{ G(a, v, F) : F not a Hamiltonian path of T\{a} } + linear + aux.
If PN_m held for all m, every unit would contribute only at T with T\{a} = vertex set of a path
of its hinge forest: at most C(N-1, 2) sets T, giving |K| >= C(N,m)/C(N-1,2) (exponential).
- pn_test.py (evaluation rank mod p, S_m-symmetrised, heads |v_t| <= R):
  m=5: R=1,2,3: max NOT in span (nopath).  m=4: trivially true (all 3-vertex trees are paths).
  m=5 all forests: max IN span already for R=1 (sanity).
- flag_test.py: coordinate-flag invariants do NOT separate (all-ones is in the span of the
  tau-vectors of star germs, m=5, R<=3). So any proof of PN_5 must use more than coordinate flags.
Status: measured only; heads unbounded in general -> open (see step 4: refuted at R=5).

### 4. Historical arbitrary-head PN_5 probe (measured; scope corrected above)
pn_test.py m=5 nopath: R=4 max NOT in span, R=5 max IN span (logs/pn5_nopath_R45.log).
This is evidence within a sampled arbitrary-head model. It does not certify a
function identity or show realizability as a connected top germ of an original
tree unit. The newer canonical-head reduction and exact five-label certificate
supersede the earlier conclusion that actual five-label path necessity fails.
Flag invariants with subset flags (flag_gen.py) do not separate even at R=1.
sym_span.py (S_N-orbit families "centre + <=k special vertices + one class of generic
leaves", polynomial orbits): N=5 k<=2 IN (trivial), N=6 k<=1,2 NOT in span.

### 5. Quadratic bound holds for all tree units — LEAN VERIFIED
MaxCaterpillar/Trees/Quadratic.lean: TreeFace (apex, head vertex, parent map with decreasing
depth = arbitrary spanning tree of the non-apex labels, per-edge orientation and state),
IsTreeExpansion, tree_expansion_quadratic: N(N-1) <= 6|K| (axioms propext/Quot.sound/choice);
generic count_lower_of_good. Aggregator MaxCaterpillar/Trees.lean builds.
The Lean proof of caterpillar_count_lower only uses Good D apex (sum h = 0, h_apex = -1,
pairs avoid the apex, |M| <= N-2), which every tree face function satisfies. Stars attain
the per-unit maximum N-2 of passed 3-sets, so passing-locality counting cannot beat
N(N-1)/6 for trees.

### 6. PRIORITY TASK (coordinator): vocabulary of Brunck et al. = caterpillars + rooted stars
STATUS: LEAN VERIFIED. File MaxCaterpillar/Trees/RootedStars.lean
(axioms propext, Quot.sound, Classical.choice; `lake build MaxCaterpillar.Trees.RootedStars` ok).
- rootedStar a c y = relu(y_c - y_a + sum_{l != a,c} relu(y_c - y_l))  (= h_pyr(B_{a,pi,empty}) - y_a).
- rootedStarFace a c Lin: faces keeping every leaf edge (linear for l in Lin, hinge otherwise).
  Faces that OMIT a leaf edge s are caterpillar faces (paper proof: caterpillar with spine c -> s,
  all other labels leaves of c, edge (c,s) linear; exact check star_faces_check.py N=4,5,6:
  every non-caterpillar, non-auxiliary star face has no omitted leaf).
- mixedDiff_rootedStarFace: for 3 <= k <= N-1 the k-th mixed difference kills every such face
  (c tied: an untied coordinate makes the preactivation >= 1 - delta(N+1) > 0 on the box, so the
  unit is a sum of 2-coordinate functions; c untied: preactivation = integer - (nonneg box offsets),
  so the unit is 0 or affine on the box).
- Public: IsRootedStarExpansion r K (K caterpillar descriptions, arbitrary coefficients on all
  rooted-star faces (a,c,Lin), aux), rootedStar_expansion_choose_le: C(N,k) <= 6^k |K| for
  3 <= k <= N-1; rootedStar_expansion_exponential (N >= 4): 7^N <= (N+1) N^2 6^N |K|.
- Their construction size (question 2): not computed. Top identity (Sec. 7.1):
  MAX_n = ((-1)^n/n!) sum_v sum_pi sum_M (-1)^|M| h_pyr(B_{v,pi,M}) + R_{n-1}, all N!(2^{N-2})
  signed paramid terms (collapsing to the distinct caterpillar pyramids plus N(N-1) stars),
  remainder R_{n-1} handled recursively; widths not stated (best5/lit/LITERATURE.md).

### 7. Bounded hinge degree: exponential — LEAN VERIFIED
Claim: if every tree unit's hinge forest has max degree <= Delta, then
C(N,k) <= 2 (12 Delta - 6)^k |K| for 3 <= k <= N, so |K| >= (1 + 1/(12 Delta - 6))^N / (2(N+1)).
Proof: (a)+(s) force isolated vertices (in T iff kappa != 0); the forest orientation outside T
is unique (leaf argument via max depth); hinge edges outside T >= e - Delta k contain a matching P
with (2Delta-1)|P| >= e - Delta k; orders <= k!(N-k)!/2^|P|; #T <= C(2e, j) <= 2^p (6A)^k via
(1+1/(3A))^(2A) <= e^(2/3) <= 2. Also superpolynomial for Delta = o(N/log N).
Lean (all build; axioms propext/Quot.sound/Classical.choice):
- Trees/DescrPass.lean: descr_pass_of_mixedDiff_ne, descr_balanced_of_arg_eq_zero ((a),(s) for any
  description with integer head and pairs i<j).
- Trees/BoundedDegree.lean: one_add_pow_le_two, choose_le_aux, exists_matching,
  orient_eq_of_balanced, card_balanced_fiber, card_passes_le (per unit <= 2(6(2D-1))^k k!(N-k)!).
- Trees/BoundedDegreeMain.lean: TreeFace.hingeDeg, tree_bounded_choose_le
  (C(N,k) <= 2 (6(2D-1))^k |K|, 3<=k<=N), tree_bounded_exponential
  ((6(2D-1)+1)^N <= 2(N+1)(6(2D-1))^N |K|, N>=3).
Not added to any aggregator (MaxCaterpillar.lean / Trees.lean untouched).

### 8. Hub class (bounded degree + rooted stars in one statement) — LEAN VERIFIED
HubOK D Δ: every hinge neighbour of a vertex of hinge degree > Δ has κ ≤ 0.
Contains trees of hinge degree <= Δ (hubOK_of_hingeDeg_le) and the rooted stars of Brunck et al.
(starFace a c, starFace_unit = rootedStar, starFace_hubOK).
Proof: tied hub ⇒ all neighbours tied; non-hub vertices with only hub neighbours are forced
(tied iff a hub neighbour is tied or κ ≠ 0); (Δ+1)·#tied hubs <= 2k (edges inside T <= k via the
child map); matching on non-hub edges outside T.
Lean (axioms propext/Quot.sound/Classical.choice):
- Trees/Hubs.lean: card_balanced_fiber_of_matching, nbr_mem_of_hub, mem_tie_of_rest,
  card_tied_hubs, card_passes_le_hub (per unit <= 2(k+1)(6A)^k S k!(N-k)!, S = sum_{i<=2k/(Δ+1)} C(N,i)).
- Trees/HubsMain.lean: choose_le_of_hubs, tree_hub_choose_le, tree_hub_exponential
  (Δ >= 3, 3 <= k, (144(2Δ-1)^2+1)k <= N  ⇒  2^k <= 2(k+1)^2 |K|), starFace, starFace_unit,
  starFace_hubOK, tree_star_or_bounded_exponential (every unit a rooted star or of hinge degree <= Δ).
Here the rooted stars ARE counted in K (unlike rootedStar_expansion_exponential).
Not covered: caterpillars with long-leaved spines (their hubs have κ>=1 spine neighbours) and
out-stars (leaves κ = 1). The residual obstruction for arbitrary trees is exactly hubs with many
κ>=1 neighbours: a tied out-star centre lets all its leaves be untied in every order.

### 9. One theorem: caterpillars + rooted stars + bounded degree — LEAN VERIFIED
Trees/Combined.lean: exists_passes_mixed, choose_le_mixed
(C(N,k) <= 6^k |K1| + 2(k+1)(6A)^k S |K2|), IsMixedExpansion, mixed_expansion_exponential:
K1 caterpillar face descriptions, K2 tree faces with HubOK (rooted stars via starFace_hubOK,
bounded hinge degree via hubOK_of_hingeDeg_le); Δ >= 3, 3 <= k, (144(2Δ-1)^2+1) k <= N
⇒ 2^k <= 2(k+1)^2 (|K1|+|K2|). Axioms propext/Quot.sound/Classical.choice.
(The s-extension of the hub class was not needed for this: caterpillars use their own 6^k bound.)

### 10. (b) Germ-level elimination of out-star germs (proved on paper; checked exactly m = 4..11)
Out-star unit S+_{a,c} = relu(y_c - y_a + sum_l relu(y_l - y_c)); at an m-tie T containing a, c its
germ is s_ac = relu(z_c - z_a + sum_{l in T} relu(z_l - z_c)) (untied leaves lie below c), independent
of the order of the untied coordinates; otherwise its germ is linear or zero.
Explicit functional (m >= 4): Lambda = sum_{t in T} MD_{delta^(t)} - (m-1) MD_{1}, MD_delta f =
sum_{S subset T} (-1)^{m-|S|} f(delta_S), delta^(t) = 1 except D = m-2 at t.
Lambda(max_T) = (-1)^{m-1}; Lambda(s_ac) = 0 for all a != c (paper proof: big step at a gives 0,
big step at c or a leaf gives (-1)^{m-1}, unit steps give (-1)^{m-1}; outstar_lambda.py exact m=4..11).
Lambda is a combination of mixed differences, so every non-passing unit is still killed: the
caterpillar counting C(N,k) <= 6^k |K| survives adding all N(N-1) out-stars (uncounted), k >= 4.
Lean not done (needs mixed differences with unequal steps / shifted bases in the pass lemmas).
Stronger, measured: MD combinations kill ALL germs having a vertex with >= 2 out-leaves
(leaf l, term relu(z_l - z_c), v_l = 0) but not max_m: m=4 (R<=2), m=5 (R<=4)
(twoleaf_md.py, logs/twoleaf_5.log, logs/twoleaf_more.log). Germs with >= 1 out-leaf span max
already at m = 3 (outleaf_test.py), so "one out-leaf" cannot be eliminated.
If the >=2-out-leaf elimination holds for all m, a tied hub contributes at most one tied
out-leaf per locality, which would remove the out-star obstruction to counting for arbitrary trees.
m = 6 test needs a symmetry-reduced, vectorized instrument (naive run too large; stopped).

### 11. Symmetry-reduced instrument; elimination of >=2-out-leaf / twin-leaf germs (measured)
sym_md.py: S_m-symmetric origin tests T_p = sum over the orbit of a step multiset p of the mixed
difference at the full tie; evaluate only orbit representatives (apex 0, canonical form).
A separating symmetric functional exists iff max's test vector is outside the family's span.
Family "two" (a vertex with >= 2 out-leaves: leaf l, term relu(z_l - z_c), v_l = 0):
  m=5: R<=8 SEPARATED; m=6: R=1..5 SEPARATED (R=3 needs >=7 step values; with 5 values the
  210 tests were insufficient: "not separated" was an instrument artefact, rank 100 < 135 later);
  m=7 R=1 (5 step values, 330 tests): SEPARATED; m=7 R=2 running (logs/sym_md_7.log).
  Logs: logs/sym_md_6.log.
Family "twin" (two leaves of F at a common centre with the same orientation and head entry):
  m=4,5 (R<=5), m=6 (R<=2): SEPARATED (logs/sym_twin.log).
Structural fact (proved on paper): a germ with twin leaves l1,l2 has no wall on the hyperplane
z_l1 = z_l2 (its gradient components on l1,l2 lie in the same set {v, v±1}, which never gives a
normal parallel to e_l1 - e_l2), while max_T has a wall there. Coordinate-flag (top-degree)
invariants do NOT separate (twoleaf_flag.py, m=4,5): the separating functionals use boxes with
comparable step sizes. Explicit functional for general m: NOT FOUND (the m=5 solution
from sym_extract.py has 12 patterns with irregular rational coefficients).
The out-star functional Lambda of step 10 does not kill general >=2-out-leaf germs
(lam_on_family.py: 600/1440 nonzero at m=5).
Counting sketch if twin elimination holds for all m: a tied centre has at most one tied F(T)-leaf
per signature (orientation, kappa); hub-style forcing for kappa<=0 neighbours; residual loss from
many signature classes appears to be e^{o(N)} (classes with kappa value K need K-1 further
neighbours, so <= O(N^{1/3}) classes of size O(N^{1/3})) -- NOT written out, not checked.

### 12. Recursion-on-m route (analysis; no general proof)
Reductions for a homogeneous germ f on R^T and t in T: L_t f / U_t f = face germ of f in
direction -e_t / +e_t, restricted to z_t = 0 (limits of the m-th mixed difference with a huge step
at t: MD = MD'(U_t f) - MD'(f|z_t=0), and with the box anchored at -D e_t: MD'(f|z_t=0) - MD'(L_t f)).
Proved on paper:
 (i) L_t, U_t preserve "no wall on H_ij = {z_i = z_j}" for t not in {i,j} (a face germ has lineality
     e_t, so restricting to z_t = 0 creates no new wall on H_ij);
 (ii) twin germs (and the generalised class relu(B(z') + phi(z',z_l1) + phi(z',z_l2))) have no wall
     on H_{l1 l2} and the class is closed under L_t, U_t for t not in {l1,l2} (or becomes linear/0);
 (iii) Delta_t = L_t - U_t maps max_r to max_{r-1} + linear, kills sigma(z_i - z_j) for t not in {i,j}
     and maps every auxiliary function to a linear function or 0;
 (iv) hence for each pair {i,j} and each order of the other coordinates, the chain functional
     C = (coefficient of relu(z_i - z_j) after applying Delta along the order) satisfies C(max) = 1,
     C(aux) = C(linear) = 0, and C(G) = 0 for every germ G with twins AT {i,j}.
Obstruction: C kills twins only at its own pair. Counting with per-pair detectors is provably too
weak: a "double out-star" unit (two adjacent hubs, each with ~N/2 kappa=1 leaves) has twin pairs
only inside each half, covers a constant fraction of the pairs at ~C(N/2,m/2)^2 ~ C(N,m)/sqrt(m)
tie sets, so per-pair counting gives only a polynomial bound. A single functional killing ALL twin
germs is needed. Sums of chain functionals over pairs do not cancel the contributions of chains whose
final pair is not the twin pair (twin symmetry pairs chains with EQUAL values, Delta_{l1} G = G minus
leaf l1). Coordinate-flag (top-degree) invariants do not separate (step 11). The out-star functional
Lambda kills germs with >= m-2 out-leaves at a centre (lam_r.py: m=5 r=3, m=6 r=4: all zero) but not
>= m-3 (m=6 r=3: 4320/8640 nonzero).
Status: general-m twin elimination OPEN (measured true for m <= 6 and m = 7, R = 1); no PROOFS.md entry.
m=7 R=2 run still in progress (logs/sym_md_7.log; slow canonicalisation).

### 13. Historical all-head twin probes: m = 4 exact; bounded-grid failures at m = 5
Reformulations (proved on paper, elementary):
 (a) MD functionals = pairings with D = d_1...d_m.  A PL function with all m-th mixed differences zero is a
     sum of PL functions each independent of one coordinate (ANOVA: f(z) = -sum_{S != [m]} (-1)^{m-|S|} f(z_S)).
     So a twin-killing Phi_m (killing W_m = sum_i {f independent of z_i}) exists for heads <= R iff
     max_m is not in span(twin germs, heads <= R) + W_m.
 (b) Unit-cube form: on diagonal-invariant germs every integer-box MD functional is
     Phi_W f = sum_{ybar in Z^m / Z.1} W(ybar) U_ybar f  (U_y = MD on the unit cube anchored at y), and
     U_y(max) = (-1)^{m+1} [y in Z.1], so Phi_W(max) = (-1)^{m+1} W(0).  Origin-anchored positive steps
     are WLOG (diagonal translation + inclusion-exclusion); MD_delta max = (-1)^{m+1} min(delta).
 (c) D max restricted to 1^perp is the point mass at 0 (Fourier transform constant).
m = 4 (EXACT, twin_m4_check.py): W = 1 on the S_4-orbits of (0000), (0022), (0111), (0122) and 2 on the
orbit of (0222) gives Phi(max) = -1 and Phi(g) = 0 for every twin germ at a 4-tie, all labelings and ALL
kappa (Phi(g_kappa) is PL in kappa with kinks |kappa| <= 12; checked |kappa| <= 60).  At m = 4 the twin family
is {relu(-z_a + (1-2k) z_c + k(z_1+z_2) + relu(z_1-z_c) + relu(z_2-z_c))} (in-orientation = out at k-1).
m = 5 (measured, twin_wsep.py, anchors normalised min 0, entries <= k): separation holds iff k >= R+1 in all
runs: R=2: k=4 yes (k=2,3 no); R=4: k=5 yes, k=4 no; R=6: k=7 yes, k=5,6 no; R=8: k=9 yes, k=5..8 no;
R=10: k=11 yes, k=9 no.  For each fixed k the family rank saturates (k=5: rank 106 at R=6 and R=8; k=6: 189)
with max INSIDE.  Same failure when only the twin leaves' heads are bounded (|kappa| <= 1, others <= R).
The measurements suggest that these bounded grids need finer resolution as R
grows. They do not quantify over all rational boxes and do not prove
nonexistence of a finite uniform functional. Per-R separation still holds
in the measured range R <= 10.
Closure probe (twin_limit.py, generic boxes): adding head-limit functions 1[<l,z> > 0] * L0 (limits of
twin germs with heads v0 + lambda l, l_apex = 0, l equal on the twin pair) adds 1 dimension and keeps max
separated (m=5, R <= 4, |l| <= 2): no sign that max lies in the closure, so a continuous (non-finite)
uniform functional may exist.
Wall-density functionals (twin_jfam.py: MDs of the H_12 jump density J_12 f, symmetrised; they kill W
and twins at their own pair) do NOT separate even at m = 4.
One-huge-step limit functionals (twin_hier.py: sum_t Psi o Delta_t with Psi an (m-1)-dim unit-anchor
functional, D = 10^7, plus m-dim anchors) with fixed spreads also lose separation as R grows (m=5: k1<=6,
k2<=5 fail at R=4..8).
Continuum probe (twin_l2.py, L^2 on 2500 random chamber points of the symmetrised MD transform):
relative residual of max against span(twins, heads <= R): m=4: 0.109, 0.059, 0.048, 0.045, 0.044 (R=1..32,
stable -> consistent with the uniform m=4 functional); m=5: 2.2e-2 (R=1), 8.3e-3 (2), 8.6e-3 (3), 5.7e-3 (4),
4.9e-3 (6), 3.6e-3 (8), 3.9e-3 (10) (logs/twin_l2_5.log; numerical ranks 36/64/102/200/330/492 = exact ranks).
Decreasing, possibly levelling off; INCONCLUSIVE whether max lies in the closure at m=5.
New separation data (generic symmetric tests, sym_generic.py, validated: m=6 R=3 "two" rank 135 as before):
m=6 twin R=3 (3142 germ reps): rank 849, with max 850 -> SEPARATED (logs/gen_twin_6_3.log).
m=7 "two" R=2 (old run "not separated" with 6 step values, 792 tests, rank 610): re-test with generic tests
DONE: SEPARATED (900 generic tests, rank 663, with max 664; logs/gen_two_7_2.log) -> the old m=7 R=2
"not separated" was an instrument artefact (too few step values).
Historical status: per-R twin elimination was measured for m<=6, including
m=5 up to R=10. The all-head uniform question was unresolved. The present
canonical-head reduction removes arbitrary heads from the top-quotient route,
so these resolution measurements do not block the current uniform twin lemma.

### 14. Closure question at m = 5: max_5 IS (numerically) in the closure of span(twin germs, all heads) + W_5
Structural facts (paper):
 (i) every germ with apex a is g = relu(A(z_{-a}) - z_a) with A = <v',z'> + sum_F relu(z_i - z_j) a PL
     function of the other coordinates; max = z_0 + relu(max_{T\0} - z_0) has the same form.  Pairing D g with
     sigma(z_a) tau(z') where sigma = 1 on a long interval reproduces Delta_a (step 12): nothing new.
 (ii) heads v = v0 + lam u (u in M = {x_apex = 0, sum x = 0, x_l1 = x_l2}, dim M = m-3) give, as lam -> oo,
     g - lam relu(<u,z>) -> 1[<u,z> > 0] L0 plus distributional terms L0^k delta^(k-2)(<u,z>) lam^(1-k);
     relu(<u,z>) and 1[u.z>0] * (terms without z_apex) lie in W.  Uniform killing therefore needs the
     conditions for every real direction u in M.  At m = 4, dim M = 1 (finitely many directions): the uniform
     finite functional of step 13 exists.  At m = 5, dim M = 2 (a circle of directions): this explains why
     every finite-spread functional fails once R >= spread (step 13).
Measurements (twin_l2.py, column-normalised SVD; 5000 chamber points of the symmetrised box-MD transform,
i.e. pairings of D f with box indicators = a weak (negative-Sobolev-type) norm; logs/twin_l2_5c.log;
held-out validation twin_l2_holdout.py, logs/twin_l2_holdout_5.log, fit on half, test on the other half):
   R        2        4        8        12       16
   train  7.0e-3   4.5e-3   2.2e-3   1.2e-3   7.5e-4   (ranks 36, 102, 330, 686, 1170)
   test   7.1e-3   4.8e-3   2.7e-3   1.75e-3  1.35e-3
 m = 4 for comparison: 0.107 (R=2), 0.047 (8), 0.043 (32): stable plateau.
 (Earlier step-13 numbers for R >= 10 were QR-tolerance artefacts; superseded.)
First-order limit functions alone (twin_l2lim.py, 1[u.z>0](Phi_F - z_0), 1[u.z>0]<w,z>, real u) barely move
the residual (8.3e-3 -> 7.4e-3 at R=2): the approximation of max comes from finite-but-large heads.
CONCLUSION (measured, not proved): the relative distance from max_5 to span(twins, heads <= R) + W_5 decays
roughly like R^(-0.8) on held-out points, so max_5 lies in the closure: no continuous (head-uniform)
twin-killing functional exists at m = 5, in addition to no finite one.  Exact per-R separation still holds
(R <= 10, step 13), so there is no exact identity with heads <= 10; an exact identity max_5 = twins + W would
need either heads > 10 or would contradict per-R separation.  Closure membership alone gives no exact tree
expansion (the error must be absorbed by non-twin germs), so it does not by itself yield a subexponential
construction; it does mean any twin-elimination proof must quantify heads (margin ~ 1/R).
m = 7 "two" R = 2: SEPARATED with generic tests (step 13 entry updated).
