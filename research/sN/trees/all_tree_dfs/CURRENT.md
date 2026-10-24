# Exponential width: current DFS record, 24 October 2026

The uniform exponential upper construction and the unrestricted all-tree
exponential lower bound are **not proved**. Two tree-based exponential-size restrictions
are now rigorously ruled out: one-descent orders at six inputs, and the
noncrossing members of the present caterpillar dictionary at eight inputs,
even with rooted-star faces added. The latter works at six and seven inputs,
so the eight-input obstruction is a real boundary. The lower search has a new
unrestricted cubic bound and reduces an exponential bound to uniform canonical
twin separation. None of these new finite certificates is part of the Lean
verification receipt.

## Upper target and what would suffice

Keep the ordinary two hidden layers, zero biases, first hidden layer consisting
of the global coordinate channels and functions `σ(x_i-x_j)`, and equality on
all real inputs. Seek a constant `C` independent of `N` with second hidden layer
width `poly(N) C^N`.

Fix the cyclic order `0,1,…,N−1`. A larger remaining candidate `NC_N` allows
every noncrossing tree shape, arbitrary edge orientations, and any root in
the head `x_root−x_apex`. This is larger than the paper's caterpillar
dictionary, even on some caterpillar-shaped trees. **The head edge from root
to apex is not required to be noncrossing.** The sufficient upper lemma is

\[
h_{\Delta_N}\in\operatorname{span}\{h_Q:Q\in NC_N\}+L_{N-2}
\qquad\text{for every }N.
\]

The paper's residual-reduction argument works for any finite polytope family:
an actual top-class identity implies exact simplex representation by all faces
of the same polytopes plus linear functions. Thus this one uniform identity
would already suffice. It does not require a separate recursive network or a
factorial number of lower-arity copies. See the proof in
[the independent review](../all_tree_review.md).

The family is exponentially sized. A noncrossing tree on `n=N−1` cyclically
ordered vertices extends to a polygon triangulation. There are at most `4^n`
triangulations and at most `2^(2n−3)≤4^n` edge subsets of each, so there are at
most `16^n` such trees. Count `N(N−1)` choices of apex and root and at most five
distinct states per unoriented edge: omitted, either linear orientation, or
either hinge orientation. Even the larger family of all noncrossing tree face
functions therefore has fewer than `N²80^N` descriptions. The uniform lemma
would give second width at most `N²80^N+2` and the same quadratic first width.
This loose bound is conditional, not an achieved asymptotic theorem. The same
lemma restricted to the present caterpillar dictionary is false at `N=8`.

The known factorial dictionary-dimension lower bound does not obstruct this:
it concerns spanning the entire dictionary modulo auxiliary functions, whereas
we seek a sparse representation of one specified function.

## Exact finite upper results

| Family / arity | Evidence | Conclusion |
|---|---|---|
| Orders with at most one descent, `N=5` | 270 nonzero units; 1,970 independently regenerated exact chamber equations and 3,125 direct integer evaluations | Exact network exists with second width 272 |
| Same one-descent family, `N=6` | 717 top columns; modular augmented rank 712; six independent formal rational identities force ordinary rank at most 711 | The entire face dictionary is insufficient, even modulo `L_4`; adding all rooted stars still fails (12 exact relations, ranks 735/736) |
| Noncrossing caterpillars, `N=6` | 1,860 available units; 528 selected units in 45 dihedral orbits; all complete face flags equal the simplex exactly | Genuine top identity modulo `L_4`, hence exact face-dictionary sufficiency |
| Noncrossing caterpillars, `N=7` | 11,403 available units; 6,909 selected units in 497 dihedral orbits; exact symbolic rational identity | Genuine top identity modulo `L_5`, hence exact face-dictionary sufficiency |
| Noncrossing caterpillars, `N=8` | 66,416 full units in 4,165 D8 orbits; all 68 independent kernel identities checked exactly; augmented modular rank 4,098 | Exact impossibility: ordinary rank at most 4,097, even modulo `L_6` |
| Add rooted-star faces, `N=8` | One additional exact star relation; ordinary rank at most 4,100, augmented rank 4,101 | Exact impossibility remains |
| Add all noncrossing subdivided claws with arbitrary source/root pair, `N=8` | Add 12,544 units in 784 orbits; 4,979 frequency rows give ranks 4,865/4,866 | No positive result; this larger family's rank gap is still only a modular diagnostic |
| Add all source/root markings of noncrossing Hamiltonian paths, `N=8` | 87,920 units in 5,513 orbits; 5,543 rows give ranks 5,315/5,316, independently replayed | Modular diagnostic only; does not rule out all noncrossing trees |

The six- and seven-input counts refer to full pyramids before face corrections;
they are not the final numbers of second hidden layer neurons. No explicit
complete coefficient array for those face corrections is claimed here.

The rational functions use frequencies `Σ_i ω_i=0`. For a canonical root-head
tree unit, let `a` be its apex and let `q_e` sum the frequencies in the component
away from the root. With `ε_e=+1` if the source of `σ(x_i-x_j)` is on that
component and `ε_e=−1` otherwise,

\[
R_U(\omega)=\frac{(-\omega_a)^{N-4}}
 {\prod_e q_e(q_e+\varepsilon_e\omega_a)},
\qquad R_{\max_N}(\omega)=\frac{(-1)^{N-1}}{\prod_i\omega_i}.
\]

These omit the common Fourier factor `i^(−N)`. The sign in the maximum formula
matters at even arity. Every missing or linear edge state has smaller dimension
and disappears from this top quotient.

`rational_identity.py` proves rational identities by exact principal parts and
polynomial interpolation, recursively eliminating variables; it does not rely
on a sampled rank. The independent audit checked the algorithm and 96 exact
identity/perturbation controls. The Fourier-to-class bridge is proved in
Section 8 of [the review](../all_tree_review.md): residues at facet-direction
hyperplanes recover the opposite-face derivative, so induction and the paper's
reconstruction theorem give `R_f=0 iff f∈L_(d−1)`. This also recovers every
complete face flag. Hence the seven-input symbolic identity has the same
geometric meaning as the six-input full-flag certificate.

Key receipts and producers (use the existing research virtual environment):

```sh
P=research/sN/dfs/h4-general-neurons/venv/bin/python
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/dfs_review_upper_certificate.py
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/dfs_review_upper_obstruction.py
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/all_tree_dfs/nc_top.py 6
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/all_tree_dfs/rational_identity.py 6
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/all_tree_dfs/rational_identity.py 7
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/dfs_review_rational_verifier.py
```

The sparse one-descent coefficient certificate is `cyclic_upper_5_desc1.json`.
The impossible six-input family is documented by
`upper_rank_certificate_6_desc1.json` and the independent
`../dfs_review_upper_obstruction_6.json`. Noncrossing coefficients are in
`nc_top_6.json` and `nc_fast_7.json`; their exact receipts are
`nc_top_6.log`, `nc_rational_identity_6.json`, and
`nc_rational_identity_7.json`. The final negative receipt is
`nc_obstruction_8_certified.json`. Its first 66 symbolic identities passed in
the 900-second run; separate checks certified the last two. The original
large modular matrix is losslessly compressed as `nc_fast_8.json.gz`, with
its uncompressed and compressed hashes in `nc_fast_8.compression.json`.

For the large modular rank proposals, `nc_refine.py` uses `python-flint 0.9.0`.
The exact rational identity checker itself uses only the Python standard
library. The environment was Python 3.12.3, NumPy 2.5.4, SciPy 1.18.1,
SymPy 1.14.0. The aggregate obstruction can be reproduced by
`nc_obstruction.py 8 short`, followed by `nc_obstruction_chunk.py` for any
remaining identities and `nc_finalize_obstruction.py`; input metadata and
kernel proposals are retained. Modular ranks are independently reproducible
with `nc_refine.py 8` and the saved frequencies.

## Upper DFS branches and next mathematical test

1. Cyclic and dihedral label orders alone: the five-input LP reported
   infeasibility. This floating solver report is not an exact impossibility
   certificate.
2. At most one descent: exact five-input success, then exact six-input
   refutation, also after adding rooted-star faces. The original all-row LP hit its 300-second limit; a 60-second
   constraint-generation attempt also timed out. Those timeouts were not used
   as mathematical evidence. The later rank obstruction closes the route.
3. Naive two-shuffle averaging: not a symmetrizing projection; its invertibility
   does not sparsify a general orbit sum. Any repaired construction must use
   relations among different cuts/face states.
4. Noncrossing caterpillars: exact successes at six and seven, exact failure
   at eight, including rooted-star faces. The initial 180-second test stopped
   before detecting this gap; a completed rank computation and 68 exact
   identities establish it. Individual
   crossing terms cannot always be uncrossed: alternating-cut poles can occur
   in crossing terms but never in a noncrossing term. The cancellation must
   occur across a combination before reducing its crossings.

The proposed saturation statement for noncrossing caterpillars in the earlier
review is therefore refuted, even for the coordinate-only fraction. A repaired
route must enlarge the vocabulary. The first noncaterpillar shape appears
exactly at eight inputs: the subdivided claw. Adding that shape with the
tested source/root orientations did not remove the modular gap. Another
enlargement permits all marked source/root pairs even on caterpillar-shaped
trees, rather than requiring their connecting path to contain every nonleaf.

For any tree oriented away from a source `s`, with marked root `r`, its unit is
`σ(B_T+x_s+x_r−x_a)`, where
`B_T=Σ_{uv∈E(T)}max(x_u,x_v)−Σ_{v∈T}x_v`. Thus source/root exchange gives the
same unit. On Boolean inputs `B_T(1_S)=cc(T[T\\S])−1`, connecting this larger
family to induced-forest component counts. The review records the exact
Boolean top coefficient and its branch factorization. This is a useful
identity, not a uniform upper construction.

A possible residue argument for the larger family must cancel forbidden
alternating-cut poles collectively. At a cut pole, the tree rational function
factors into the two cut components. One component has total frequency zero
and retains the apex frequency as an external parameter, so an induction must
include these boundary parameters. An ordinary smaller-arity induction does
not yet close. The exact factorization and the proposed saturation statement
are written in the review. No unproved saturation claim is being assumed.

## Unrestricted all-tree lower bound

The model is `Trees.TreeFace.unit`: arbitrary original tree shape, arbitrary
root and edge orientations/states, with head `x_root−x_apex`, plus the paper's
auxiliary span. It is not a claim about arbitrary real head vectors.

For a connected top germ at a tied set, outside balance forces the head to be
`e_root'−e_apex`: sum coefficients over each outside component, which attaches
at a single tied vertex. This removes the arbitrary-head overapproximation
that obscured the earlier searches. The proof and exhaustive definition-level
checks through six inputs are in the review.

An exact five-label flag functional annihilates every canonical nonpath tree
(a star) modulo `L_3`, while taking value 120 on the simplex. Its independent
checker operates on exposed vertices rather than the producer's facet
recursion. Every five-element tie therefore needs a surviving four-vertex
path. In an `(N−1)`-vertex tree, the number of those paths is at most
`floor((N−3)^2/4)`. This gives the unrestricted mathematical bound

\[
\binom N5\leq\left\lfloor\frac{(N-3)^2}{4}\right\rfloor |K|,
\qquad |K|\geq(1/30+o(1))N^3.
\]

It improves the Lean-verified quadratic bound from `N≥9`, but the cubic result
itself is not yet Lean-verified. The stronger path-separation claim fails at
six labels: a signed combination of five nonpath symmetry orbits matches every
complete simplex flag. It is not a route to a uniform exponential bound.

The remaining sufficient lower lemma can be weakened to **outward-twin
separation**: for every sufficiently large arity, the simplex class is outside
the span modulo `L_(m-2)` of canonical tree units with two nonroot leaves at
one hub, both carrying `sigma(x_leaf-x_hub)`. The earlier stronger twin lemma
is certified at five and six labels and supported by seven-label modular
ranks83/84, so these finite cases also support the weaker statement. No
uniform separation theorem is proved.

The improved counting argument needs only this weaker lemma. In a tree on
n=N-1 vertices with matching number nu, if nu>=n/5, ancestor closure excludes
one of four patterns per matching edge. Otherwise pair original nonroot
leaves at their common hubs; there are at least(n-3nu)/2>n/5 disjoint pairs.
Head balance and exclusion of outward twins forbid at least one of four
patterns per pair, regardless of the original leaf edge states. Thus a unit
covers at most n*2^n*(3/4)^(n/5) large tie sets, giving the conditional bound
`|K| >= (2-o(1))/(N-1) * (4/3)^((N-1)/5)`, base approximately1.0592.
The detailed proof and exact boundary controls are in `../all_tree_review.md`.

### Proven broader tree class (24 October continuation)

The integrated `Simplify/CoverageMain.lean` gives an exponential lower bound
when each hub has at most a fixed number s of retained hinge leaves with
kappa=1; internal branching is unrestricted. Its constant is16(s+1)/3.
The concurrently written `Unified.lean` and `UnifiedMain.lean` improve this
via omega(v)=number of such out-leaves plus the indicator of a nonleaf
neighbour. Their types and axioms were independently checked: locally Lean
verified, not yet integrated in the stable root at this review.

A new mathematical corollary covers **every underlying tree shape**: retain
all edges, orient them away from an arbitrary source s, and use the canonical
head x_r-x_a with arbitrary root r. Kappa(v)=deg(v)-1+[v=s]+[v=r]. Only s,r can
be out-leaves. Rooting the heir cover at r makes its degree at most2 even in
the exceptional case of two such leaves at one hub. Therefore adding all
these full-hinge units to the known caterpillar/rooted-star face dictionary
preserves the base7/6 lower bound. This is nonvacuous because that known
subdictionary already spans max. The new source/root bridge is mathematically
reviewed and checked on all46,656 labelled seven-input units, not yet a Lean
declaration. Arbitrary faces of the new units need not satisfy the condition:
linearizing the outer edges of many length-two arms creates arbitrarily many
out-leaves at their shared centre. The paper now includes the sharper7/6 bound and its short covering-forest
proof; the new source/root bridge remains a mathematical, not Lean, result.

## Integration and verification

The paper now uses the rational-linear projection proof, a block-factorized
reduced-degree forest count, a third mixed difference for factorial dimension,
and a shorter geometric survival/reflection/induction argument. The stable
public theorem signatures are preserved; older verified routes are retained.

Our `python3 scripts/verify.py` run passed on 24 October with 112 statements
and 302 Lean files (`verification_gate.log`). A concurrent audit subsequently
added ten statements; the current receipt, dated 11:56 UTC, checks **122 exact
statements and 303 Lean files**, using only `propext`, `Classical.choice`, and
`Quot.sound`. All 306 recorded file hashes match the current working tree.
This is a
content-hash certificate of the working tree, not a claim of a clean committed
release. The PDF rebuilt at **35 pages**, with no overfull boxes or undefined
references. Lean links in this working draft point to local sources because
the new files are not committed. The exploratory finite certificates above
have not been added to the paper as uniform theorems.

## Cyclic-graph continuation

The separate current ledger is [cycles/CURRENT.md](../../cycles/CURRENT.md).
A fixed cycle on the nonapex labels with arbitrary orientations and face states
already fails at five inputs by an exact rank certificate. A larger candidate
allowing all noncrossing graphs (cycles included) and all face states has at
most N^2*100^N descriptions; its uniform sufficiency remains open. A single
sparse graph for the entire first hidden layer cannot scale: the existing
four-label claw lemma forces every vertex to have at most two nonneighbors.
This does not exclude varying cyclic graphs between individual units.

The final continuation PDF is36pages after adding the source/root covering
proof. Its new mathematical bridge has an independent prose audit. The earlier
35-page build and122-statement certificate reported above are historical; a
concurrent Lean cleanup is moving source modules and requires a fresh global
verification receipt. No production Lean source was edited by this continuation.

The count and dimension modules have since been consolidated by the concurrent
cleanup into `MaxCaterpillar/Count/` and `MaxCaterpillar/Dimension.lean`. The
paper now cites the sharper out-leaf theorem `Count.outLeaf_unified_exponential`
and has175 live source links. The local verification descriptions above refer
to the pre-move declarations; a new global receipt must cover the cleanup.
