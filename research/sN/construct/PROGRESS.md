# Smaller exact two-hidden-layer constructions of max_N (research/sN/construct)

Model: first hidden layer = braid features sigma(x_i - x_j) (i != j) plus linear channels;
second layer = arbitrary neurons sigma(g), g in V1 = span{x_i, m_ij}. All checks exact (Fractions).

## Step 1. Subset dynamic programming (PROVED, paper)
Claim DP. Suppose for every k >= 5 there is a combination F_k of n_k second-layer neurons on
k variables (braid features only) with
    F_k = c_k max_k + sum_{T proper subset of [k]} a_T max_T + (V1),   c_k != 0.
Then max_N has an exact network with first width C(N,2)+O(N) and second width
    h2 <= C(N,3) + C(N,4) + sum_{k=5}^N C(N,k) n_k.
Proof: induction on |S|: max_S lies in span{F_T (T subset S, |T|>=5)} + span{max_T, |T|<=4}
+ V1; max_T for |T| = 3, 4 is one neuron (max_4 = m_ab + sigma(m_cd - m_ab)), |T| <= 2 is in V1.
All copies F_T use the global braid features.  So n_k = poly(k) b^k gives h2 = O((1+b)^N poly).
Key point: the recursion is a SUM over subsets, so lower terms are shared (no N! blow-up).

Useful facts (proved, paper):
- L1. span{max_T : T nonempty} = all continuous braid-PL functions (PL on the braid fan,
  positively homogeneous) = support functions of virtual generalized permutohedra.
  Proof: such F is determined by F(1_S) (rays of the simplicial braid fan) and F(1); the
  (2^k-1)x(2^k-1) matrix [S cap T nonempty] is invertible.
- L2 (top formula). For braid-PL F = sum_T a_T max_T:  a_[k] = sum_S (-1)^{|S|+1} F(1_S).
  On a neuron sigma(g), g in V1, g(1_S) = l(S) + w(S, S^c) is a QUADRATIC pseudo-Boolean
  'cut' function; along a chamber (maximal chain of subsets) the neuron is the 'walk'
  (g(S_1),...,g(S_{k-1})): one-signed walk = linear piece, mixed walk = non-braid crossing.
- L3 (equivalence). Let tau_k = min #neurons (braid first layer) whose weighted sum is
  braid-PL with a_[k] != 0 ('top cost').  Then
      tau_N <= h2(max_N) <= C(N,3)+C(N,4)+sum_{k=5}^N C(N,k) tau_k
  (left: any exact network gives such a sum with a_[N] = 1; right: Claim DP + L1).
  So the exact second width equals the top cost up to a factor 2^N: an exponential
  construction exists iff tau_k <= c^k, and lower-order garbage is free if braid-PL.
- A symmetric braid-PL function is an L-statistic f = sum_r f_r x_(r), automatically in
  span{max_T}; its top coefficient is ell(f) = sum_r (-1)^(r-1) C(k-1,r-1) f_r.
- Hence for an S_k-invariant family (weights constant on orbits) it suffices: (i) the
  non-braid zero sets cancel in ONE chamber (identity order), (ii) ell(f) != 0.
  Cost n_k = total orbit size of the used types.

## Step 2. Families tested (COMPUTED, exact, symtop.py / fam_centers.py / star_top.py)
- Out-stars sigma(sum_o s_o sigma(x_o - x_c)), s in {-1..1} or {-2..2}: top NOT achievable for
  k = 4..8 (k=4..6 for |s|<=2). Stars alone are useless (even modulo lower max_T).
- One centre with in- and out-hinges, s in {-1,0,1}: top not achievable k = 5, 6.
- Double star x_a - x_c + sum_P sigma(x_o-x_a) - sum_M sigma(x_o-x_c): k=4 yes, k=5,6 no.
- Two centres, out-roles in {-1,0,1}^2 (+ centre options): k = 4, 5 YES (k=5 even exact).

## Step 3. More families (COMPUTED, exact mod-p rank + exact Fraction recheck)
S_n-symmetric families ('few distinguished vertices + roles'); TOP = some braid-PL combination
with a_[n] != 0 exists (equivalently, by averaging, ANY combination from the family):
- role blow-ups (no specials, 2 roles, W in {-1,0,1}): n=4 yes, n=5 no.
- role blow-ups, 3 roles: n=5 yes (sparse symmetric solution: 8 types, 220 neurons), n=6 NO.
- 2 centres + out-roles {-1,0,1}^2: n=5 yes, n=6 NO.
- centre + (m_P - m_Q) + star s in {-1,0,1}: n=5,6 yes, n=7 NO (fam_cps2.py).
- Rueß atoms sigma(sum_A m - sum_B m), A,B disjoint k-edge forests: k=2: n=5,6 yes, n=7 NO
  (Rueß et al. need k = floor((n-1)/2) for exactness).
Pattern (measured, n<=7): every family with a bounded number of distinguished vertices dies
about two steps after it first works.  Neurons that create the top class seem to need
~n distinguished vertices, so S_n-symmetric constructions are factorial; a subexponential
construction must pick a sparse subset of large orbits.
- tau_5 <= 3 (three Rueß k=2 atoms, also the 3-neuron core of the max_5 identity:
  -sigma(A+Q) + 1/2 sigma(u) + 1/2 sigma(v) is braid-PL with top 1; sigma(A) is conforming).

## Step 4. Gadgets (mixed differences) and tree units with heads (COMPUTED)
- Gadget Gamma(g0;H) = sum_{theta subset H} (-1)^|theta| sigma(g0 + sum_{h in theta} u_h), u_h hinges:
  vanishes on every chamber where some u_h == 0, so with H = star at a it is supported on
  {x_a = max}; it is braid-PL iff all walks g0 + u_theta are one-signed there.  Exhaustive
  check (gadget_free.py): for m = n-1 >= 3 the only valid g0 are order statistics of
  z_o = x_a - x_o (e.g. g0 = -min z or -sum z + min z), which are not 1-layer for m >= 3.
  Symmetric g0 (affine gamma) works for m = 3, not 4.  Sums of star gadgets with S_m-symmetric
  g0 (gadget_lp.py, grids 1/2..1/4): TOP for n = 4, 5 (n=5: 11 neurons), NOT for n = 6, 7.
- Coordinator hint (large heads), out-star tree units sigma(<h,x> + sum_{o in L} sigma(x_o-x_c)),
  integer head, |h_o| <= R, leaf weights {0,1}, {0,1,2}, {-1,0,1}: TOP NOT achievable at n = 5
  for R = 1..4 (fam_bighead.py).  Large heads do not rescue single-centre stars.
- Double-star tree units (centres c1 -> c2, leaves of c1 / c2 / isolated, heads |h| <= 1):
  TOP at n = 5, 6 (dstar_fast.py), NOT at n = 7 (LP infeasible, dstar_block.py).
- Double stars with centre heads |h_c| <= 3 at n = 7 (dstar_block2.py 7 1 3): UNDECIDED.
  The HiGHS feasibility LP runs out of memory (std::bad_alloc under a 3.6 GB cap,
  logs/dstar_head7_rc3.log).  Not settled; it needs a smaller orbit basis or a mod-p rank test.
- Rueß k=2 sparse MILP at n=6 (ruess_milp.py): killed for memory after building 4200 atoms;
  no minimal-support result.

## Status summary (end of this session)
PROVED (on paper, not yet in Lean): DP bound, L1 (braid-PL = span max_T), L2 (top formula),
L3 (tau_N <= h2(max_N) <= sum_k C(N,k) tau_k).
COMPUTED: tau_5 <= 3.
REFUTED, for the families listed (as candidates for all-N subfactorial constructions):
bounded-distinguished-vertex symmetric families, star gadgets, and out-star tree units
with heads up to 4.
OPEN: sparse non-symmetric top constructions; whether tau_k grows subfactorially.
No 2^{O(N)} construction and no proved improvement over the factorial-type width was found.
Nothing has been formalised in Lean (MaxCaterpillar/Constructions/ untouched).
