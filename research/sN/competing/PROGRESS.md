# Competing construction (Brunck et al., arXiv:2610.28587v1, Sec. 7.1) vs caterpillars

## Step 1 (numerical dictionary check) -- done
`check_dictionary.py`: n = 3..6, 240 random (v, pi, M), 20 random y each.
Vertices of B_{v,pi,M} enumerated from the inequalities of their Eq. (3)
coincide with the vertices of e_{pi_q} + sum_{i=2}^{n-1} [0, e_{pi_r(i)} - e_{pi_i}]
(q = max({1} u M), r(i) = max({1} u {j in M : j < i}); uniform also for M = empty).
Support function of pyr_{e_v}(B) = y_v + relu(y_{pi_q} - y_v + sum relu(y_{pi_r(i)} - y_{pi_i}));
for M != empty equals y_v + U_{perm,S} with perm = (v, pi_1, ..., pi_{n-1}), S = M - 1
(paper indexing of def:caterpillar); for M = empty equals y_v + rootedStar v pi_1.
All 4800 checks pass. No sign (-1)^{|M|} enters the individual objects (it is a
coefficient in their sum; ours is (-1)^{N+|S|}/N!, and |S| = |M|).

Non-membership plan: at y = e_c (c = pi_1) the rooted pyramid gives n-1, while
every caterpillar face function is <= the full word function <= n-2 there.

## Step 2 (Lean drafted)
- MaxCaterpillar/Competing/Defs.lean: supportFunction, pyramid, zonotope, BHRSY.{Ordering, Ordering.pos,
  hyperplane, prefixSum, parallelepiped, paramid, paramidSupport, lastMarked, markedParent,
  Ordering.word, cutSet}, caterpillarWordDescription. Imports MaxCaterpillar.Definitions (not the
  other way round: importing it from Definitions would rebuild the whole tree).
- Competing/Relation.lean: positions, zonotope coordinates, eq_of_coords, parallelepiped_eq_zonotope.
- Competing/Support.lean: support function, word dictionary, rooted stars, non-membership
  (evaluate at e_c: star = N-1, caterpillar <= N-2), converse.
- Theorems.lean: public bhrsy_* facade. Compiling (lean lock queue busy).

## Step 3 (Lean compiled, claims added)
- Competing/{Defs,Relation,Support}.lean and Theorems.lean build (lake build ... EXIT 0, no warnings in Competing).
- 11 claims appended to verification/main.json (claims.json here); exact types pre-checked, axioms
  propext/Classical.choice/Quot.sound only. Full scripts/verify.py running (verify.log).
- Lesson: in this Lean/Mathlib, omega fails on Fin.val atoms with ≠ and on ∧ hypotheses/goals and
  on beta-unreduced filter predicates; destructure and `show` first.

## Step 4 (paper)
- New appendix D `app:bsy` ("Relation to the construction of Brunck et al."): Definition `def:bsy`,
  Theorem `thm:bsy-relation` (a)-(d), proof with steps stp:bsy-*; equations eq:bsy-hyperplane,
  eq:bsy-parallelepiped, eq:bsy-marked, eq:rooted-star, eq:bsy-zonotope, eq:bsy-support, eq:bsy-word.
- Lean appendix: new subsection with listings; listing literates for π σ ≃ ≠ ∈ ∉ • ∅ ¬.
- Related work: one-sentence pointer to app:bsy.
- lean-map.json: 19 new entries. paper_links.py run with base `..` (pinned commit cannot contain
  new files), then link-config.json / \leanbase restored to the pinned commit; main session must
  re-pin after committing. PDF: 37 pages, no overfull boxes, no undefined references.

## Step 5: scripts/lean_lock.sh python3 scripts/verify.py -> PASS: 95 exact statements; 301 Lean files; only permitted axioms (verify.log).
