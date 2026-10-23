LIVE STATUS (2026-10-24): general-N question for arbitrary trees OPEN; exponential for bounded hinge degree (Lean).
Proved (Lean): quadratic N(N-1) <= 6|K| for arbitrary tree units; exponential bound for the
Brunck et al. vocabulary (caterpillars + all rooted-star faces, stars not counted).
Refuted (measured): path necessity at a 5-tie. Next test: germ functionals that use head
size / multiplicity jointly (big-head germs need non-leaf outside structure).

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

### 4. PN_5 REFUTED for larger heads (measured)
pn_test.py m=5 nopath: R=4 max NOT in span, R=5 max IN span (logs/pn5_nopath_R45.log).
So star germs (K_{1,3}) with heads up to 5 plus lower-dim tree germs produce max_5 at a 5-tie:
"path necessity" fails; any locality-type argument must use head sizes.
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
