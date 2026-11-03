# MAX5 width frontier: source and scope audit

Audit date: 3 November 2026. Model: an ordinary scalar-output ReLU network
with two hidden layers, arbitrary real weights and biases, no skips, and
exact equality with MAX5 on every real input. Both widths count physical
neurons, including neurons carrying a linear term through a hidden layer.

The currently established unrestricted table is:

| First hidden width | Second hidden width lower bound | Attained upper bound |
| --- | ---: | ---: |
| Less than 9 | Impossible at every finite second width | None |
| 9 | 4 | 11 |
| At least 10 | 4 | 6 |

The minimum possible first width is exactly nine. The certified undominated
upper pairs are (9,11) and (10,6). The second coordinates of those pairs
are not known to be optimal. In particular, neither (9,4), (9,5), nor
(10,5) is excluded by the unrestricted theorems currently audited here.

Biases do not enlarge the existence frontier: evaluate a putative biased
network at t*x, divide its output by t, and let t tend to positive infinity.
The result is the zero-bias network with the same weight matrices and
physical widths, and MAX5 is positively homogeneous. Zero-bias upper
constructions are therefore witnesses in the biased model as well.

## Evidence for the unrestricted table

**First width at least nine.** The source chain is
`research/sN/frontierN/overnight_general.md`,
`overnight_general_six.md`, and
`research/sN/best5/overnight_fixed_natural8_rectangle.md`.
The first exact finite checker covers 416 coefficient-sign profiles and
955 equations. The second covers 2,767 support multisets, 43 support orbits,
and 58,176 coefficient-sign profiles, leaving the natural eight-row bowtie.
The continuous rectangle obstruction rules out every finite second-layer
completion of that bowtie. This is a written mathematical proof with exact
finite certificates; the entire first-width theorem is not formalized in
Lean. The rectangle algebra has a Lean leaf.

**Second width at least four.** The arbitrary-bias theorem
`MaxCaterpillar.Frontier.OvernightGeneral.network_second_width_half_plus_one`
proves N+2 <= 2*h2. Substitution of N=5 gives h2>=4. The published Lean source
is [the actual-network theorem](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/9afb15c78208e8b575da3ed129a262500dc03ba0/research/sN/frontierN/overnight_general_antipodal.lean#L155).
There is no first-width or first-direction restriction in that declaration.

**Upper pair (9,11).** Exact rational physical weights are in
`research/sN/frontier5/max5_nine_c5_atoms_o2_r1.network.json`. The first
layer uses five oriented C5 comparisons and two signed coordinate pairs.
The all-input rational checker verifies 134 open first-activation/winner
cells and 157 grouped second-layer crossing ridges. Continuity covers
all remaining boundaries. This is an audited exact computation, not a
Lean theorem for these physical matrices.

**Upper pair (10,6).** Exact rational physical weights are in
`research/sN/best5/netB_10_6.json`. The checker verifies 104 open cells and
70 crossing-ridge groups. A transparent four-correction identity is proved
in `research/sN/frontier5/construction_frontier.md`; two further physical
second neurons carry its shallow head.

The fresh audit command is:

```
python3 research/sN/max5_optimal_20261103/audit/recheck.py
```

It copies the two frozen first-width checkers and their inputs to this
audit's replay directory before running them, preserving old receipts.
It also rechecks both upper constructions on all real inputs. All four
runs passed. `recheck.json` pins 26 source artifacts and records the exact
finite outputs. This is not a new Lean verification of the written bridges.

## Restricted lower bounds that must not be promoted to unrestricted ones

| Restricted class | Established lower bound or exact minimum | Principal source |
| --- | --- | --- |
| Complete comparison-plus-linear residual space, with a free shallow remainder | Exactly four folded residual terms | `research/sN/frontier5/max5_oct31_complete3_theorem.md` |
| Comparison features and one independent signed carrier pair | Physical second width at least six; attained by the bowtie at first width ten | Same source and `construction_frontier.md` |
| Arbitrarily many comparison invariant rows, arbitrary noninvariant carriers | Physical second width at least five | Same source |
| First width nine, all invariant directions coordinate differences | Physical second width at least six | `notes/max5_exact/first9_c5_lower.md` |
| Pure-C5 first width nine, arbitrary allowed carrier mixtures | Physical second width at least six; current upper eleven | Same source and `c5_four_core_child.md` |
| Seven-root catalog classes 0,1,2,3,4,8,9 with a signed carrier pair | Physical second width at least seven | `notes/max5_exact/root7_k4.md` |
| Other nine seven-root catalog classes | Physical second width at least six; attainability not asserted | Same source |
| First width nine, row-sum split (2,2,5) | Physical second width at least five, with at least three positive and two negative outputs | `research/sN/frontier5/max5_oct31_fiber_summary.md` |
| Four physical second neurons and exactly one positive output | First width at least fifteen; existence at fifteen not asserted | `notes/max5_exact/unique_positive_width4.md` |

The complete-comparison residual exclusion has two independent 35-case
CPC/Ethos packages, one per mixed output-sign count. The C5 four-residual
exclusion has five checked CPC/Ethos cases. The thirty new seven-root
cases also have independent Ethos receipts. These remain mathematical
model reductions plus external exact proof certificates, not new Lean
declarations.

The certificate title `Max5General4` is especially easy to misread. Its
four neurons are correction terms with input and first-layer skips in
the displayed functional identity. The Lean theorem `max_network`
actually constructs an ordinary network of widths (16,6), using two
additional second neurons for its remainder. See
[the exact network type](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/9afb15c78208e8b575da3ed129a262500dc03ba0/MaxCaterpillar/SmallN/Max5General4.lean#L355).
It is not an ordinary physical (h1,4) construction.

## Smallest unresolved architecture: (9,4)

The complete first-width-nine row-sum alternatives are (1,1,7) and
(2,2,5), counting positive, negative and zero row sums. The latter
alternative is excluded at second width four. Comparison-only invariant
rows are also excluded. The remaining case has an opposite signed carrier
pair and seven invariant features with at least one nonroot direction.

The carrier reduction gives

```
MAX5 = ell + R + ReLU(g) + ReLU(h),
R,g,h in span{ReLU(a_j*x): j=1,...,7},
a_j*ones=0, ell*ones=1.
```

Both residual signs must be positive. The mixed case is excluded by the
finite contact-support argument plus a physical-span contradiction, and
the two-negative case is excluded at arbitrary first width by the general
negative-core theorem. Free invariant linear functions cannot be added
to the seven-feature span.

At the five four-way top-tie contacts q_i=-e_i, both cores must vanish at
at least three contacts. The cases with exactly one or two shared contacts
have complete independent exclusions. The remaining cases are:

* **Exactly three shared contacts.** Three discrete matching patterns.
  The one-unique-contact-per-core, different-distinguished-label path case
  has all 269 support models independently refuted. The same-label case
  and the two-unique-contacts-in-one-core case remain. The same-label
  inventory has 387 surviving support classes, including six with exactly
  three physical root rows. No checked outcomes for those six were found
  in this audit; only a full same-label SMT source was found.
* **Exactly four shared contacts.** The complete decorated support cover
  has 587 cases. This audit recovered 421 distinct case indices with
  successful existing Ethos receipts and matching current source/proof
  hashes. There are 166 indices without such a recovered receipt. Old
  batch summaries undercount these completed artifacts. This inventory is
  not a fresh proof replay or a complete source-to-support-cover audit.
  `four_shared_receipt_inventory.json` lists the exact scope and indices.
* **All five shared contacts.** Nontrivial local and support restrictions
  exist, but no complete exclusion. The five-by-seven contact-value matrix
  has kernel dimension at least two automatically, so rank alone does not
  force the two cores to coincide.

Thus a lower bound five at first width nine would still require substantial
new work. Even that result would not match the current upper eleven.

## Prioritized discriminating next tests

1. Instantiate the six minimal-root same-label three-shared families with
   the audited actual-span model; determine whether they are already
   excluded by contact germs before adding expensive global conditions.
2. Recover source-to-case coverage for the 421 four-shared certificates,
   then group the 166 missing cases by support/germ mechanism. Do not
   rerun the completed cases or interpret an old batch's pending count
   as the live mathematical gap.
3. For an upper improvement, search first-nine C5/root7/nonroot spaces
   separately and use the exact all-input checker after each candidate.
   A finite-pool minimum does not prove the unrestricted minimum.
4. For a global second-width-five exclusion in the comparison-invariant
   class, the decisive residual target is a balanced two-positive,
   two-negative four-core identity in the complete comparison space.
   An arbitrary three-core exclusion does not settle this case because
   multiple carrier directions can give different tail intercepts.
5. For unrestricted second width four, retain both ordinary two-core
   identities and the compatible shifted-tail mechanism. The latter
   cannot be discarded by assuming the carrier directions coincide.

## Jensen PDF scope

The separate [PDF audit](pdf/SCOPE.md) checks the supplied manuscript.
Its page-36 statement h2(5)=4 uses the braid/skip residual convention.
Its three-core exclusion is described there as an uncertified solver
verdict; the newer repository certificates give stronger verification in
that restricted model. The manuscript supplies no new unrestricted
physical width-four or width-five construction or exclusion.
