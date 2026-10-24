# Affine breadth-first candidate

This is an exponential-size dictionary candidate for exact maximum networks
with two hidden layers. Uniform sufficiency is open. The seven-input identity
passed all exact principal-parts checks and the complete direct DFS replay.
It remains a research result; it is not a uniform width theorem.

## Family and count

On the `n=N-1` nonapex labels, label a rooted plane tree in breadth-first
order, allowing each cyclic starting position and both traversal directions.
The root defining this traversal and the root in the head are independent.
Use every canonical head `x_root-x_apex`, every edge orientation, and every
permutation `i -> a i + b (mod N)` with `gcd(a,N)=1`. The full functions are

```
sigma(x_root - x_apex + sum_(i,j in oriented edges) sigma(x_i-x_j)).
```

Include the five states of each unoriented edge: omitted, either linear
orientation, or either orientation of `sigma(x_i-x_j)`. These include the
genuine face functions of all corresponding pyramids over zonotopes.

There are at most `4^(N-2)` rooted plane trees, `2(N-1)` traversal choices,
`N` apices, `N-1` head roots, `N phi(N)` affine permutations, and
`5^(N-2)` state assignments. Thus the complete candidate has at most

```
2 N^2 phi(N) (N-1)^2 20^(N-2) <= 2 N^5 20^(N-2)
```

descriptions. This works at every arity, including composite `N`; no prime
padding or input identification is needed. The first hidden layer uses the
global coordinate channels and the `N(N-1)` functions `sigma(x_i-x_j)`.
The count is not yet an achieved width bound for the maximum.

By the reviewed general face-closure lemma in `all_tree_review.md`, a uniform
top-class identity for this family would give exact sufficiency of these
face dictionaries. There is no extra hidden layer in that bridge.

## Seven-input proposal and controls

The inventory has 6,216 of the 9,072 apex/tree graphs, 16,584 normalized
function orbits, and 696,192 full units. Thus the inventory is a proper
subfamily even at seven inputs. The previously known noncrossing
caterpillar witness has 1,428 supported full units outside this family and
does not certify this candidate.

The full modular matrix has ranks 9,348/9,348. Its particular solution has
4,068 nonzero orbit coefficients. Solving on that fixed support at six
primes and applying rational reconstruction yields a proposal using 170,835
full units. Its common denominator is
`743355437963395145137200`; numerators and denominators have at most 86 bits.
All 64 held-out rows at an unused seventh prime agree with the target.

The native evaluator was checked against 32 full NumPy rows and one complete
independent DFS-cut row. The selected-support evaluator was replayed at the
first prime against all 4,100 stored selected rows and reproduced every
coefficient. These are controls on the proposal mechanism, not the final
rational-function identity proof.

## Exact gate

`overnight_upper_modular_exact.py` decodes the shared linear-form engine into
170,836 exact rational terms, including the simplex target. Sixteen units
are checked against the separate general-head expression constructor. It
then invokes the original principal-parts verifier directly.

The independent proof-order variant
`overnight_upper_modular_residues.py` first checks exact invariance of the
whole expression under `i -> i+1` and `i -> 3i (mod 7)`. The 476 distinct
linear poles form 16 orbits under these permutations. It checks every
principal part at one representative of each orbit, using the original
rational-identity verifier on each residue. Invariance transports these
vanishing principal parts to every pole. A rational function with no finite
poles is polynomial; every term here has homogeneous degree `-7`, so that
polynomial must vanish. Each completed pole orbit has a durable checkpoint.

The pole-orbit gate passed all 16 representatives in 240.08 seconds. Thus the
seven-input top identity is exact, and the general face-closure lemma gives
finite face-dictionary sufficiency. This does not establish a uniform
construction or a Lean theorem. Full-unit counts also exclude the subsequent
face corrections and must not be reported as final network widths.

## Artifacts

- Inventory: `overnight_upper_modular_bfs_7_family.json` and its producer
  `overnight_upper_modular_family.py`.
- Rational coefficients and CRT provenance:
  `overnight_upper_modular_multicrt.json`.
- Held-out control: `overnight_upper_modular_heldout.json`.
- Exact gates: `overnight_upper_modular_exact.json` and
  `overnight_upper_modular_residues.json`, with their corresponding sources,
  run logs, and bounded-run exit records.
- Compact witness: `overnight_upper_affine_certificate_7.json`, with 914
  explicit BFS graph witnesses and all 4,068 coefficient/root/orientation
  records. Its proposal-status label is historical; the external exact gate
  above supplies the identity check.
- Complete replay: `overnight_upper_affine_replay_7.json`. The direct DFS
  expression agrees term-for-term with the controlled engine expression;
  this check also validates membership of every selected unit.

Large sample matrices and the shared native engine are reproducible proposal
artifacts, not necessary mathematical data for an independent checker that
reconstructs the rational expressions directly from the inventory and exact
coefficient vector.
