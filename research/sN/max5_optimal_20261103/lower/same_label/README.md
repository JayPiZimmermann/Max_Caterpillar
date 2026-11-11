# Six minimal-root same-label MAX5 cases excluded

All six cases below have exact CVC5 refutations independently replayed by
Ethos against their frozen formulas, with no trust rule. The necessary-model
bridge has a separate mathematical and executable audit. This is a finite
certificate result, not a new Lean theorem and not a complete MAX5 width
optimum.

## Exact scope

Consider an identity

    MAX5 = ell + R + ReLU(g) + ReLU(h),

where `ell` is linear with coordinate sum one, and R, g, h belong to the
actual span of seven oriented invariant first ReLU features. No free
linear forms are adjoined to g, h or R. At q_i=-e_i assume g alone vanishes
at q_0, h alone vanishes at q_1, and both vanish at q_2,q_3,q_4. Their
unique-contact complementary-pair germs use the same distinguished shared
label, so the three mandatory root planes are 02, 12 and 34.

There is no such identity when the four remaining physical feature
supports are any of the following multisets. Each displayed support is
exact: its coordinates are nonzero and all other coordinates are zero.
Repeated supports do not force proportional normals; all real shape
parameters and all root orientations are retained.

| Frozen cover index | Four remaining supports | Independent proof |
| --- | --- | --- |
| 275 | 012, 013, 013, 014 | CPC + Ethos PASS |
| 277 | 012, 013, 0134, 014 | CPC + Ethos PASS |
| 280 | 012, 013, 014, 034 | CPC + Ethos PASS |
| 307 | 0123, 013, 014, 014 | CPC + Ethos PASS |
| 353 | 013, 013, 014, 014 | CPC + Ethos PASS |
| 355 | 013, 013, 014, 024 | CPC + Ethos PASS |

These are exactly the six minimal-root cases in the independently audited
same-label support cover. They are six of its 387 surviving support
classes. The other 381 classes contain additional physical root rows and
are not excluded by this package. The two-unique-contacts-on-one-core,
four-shared-contact, and five-shared-contact sectors are separate.

The ordinary biased network application uses the previously established
recession and singleton-carrier reductions for a hypothetical (9,4)
network. This package does not prove a stronger unrestricted numerical
lower bound, and does not by itself show that (9,4) is impossible.

## Proof and the one extra local lemma

The unchanged audited builder imposes the unique-contact comparator germs,
shared-contact zero values, Boolean input values, and Boolean directional
germs. These are necessary equations and inequalities in unrestricted
real parameters. All enabled wall and rigidity conditions are tautological
in these six exact support classes; they add no assumption.

Five cases are refuted directly by this model. For case 277, the top
triples 013 and 014 have exactly one singular first feature each, and
that feature is nonroot. The elementary positive-two-core MAX3 calculation
forces both coefficients on that feature to be nonzero and to have equal
absolute value. The selected model adds only

    g4 != 0, h4 != 0, g4 = h4 or g4 = -h4,
    g6 != 0, h6 != 0, g6 = h6 or g6 = -h6.

Independent local core complementation changes the signs, so absolute
equality is the invariant conclusion. This lemma does not require all
five quadruple contacts to be shared. Its quantitative unit-normal
consequence and explicit sign branches were also investigated, but the
selected proof does not use them.

See `audit/AUDIT.md` and `audit/SINGLETON_AUDIT.md` for the model bridge.
The arithmetic trust boundary is the pinned Ethos checker and CPC
signature package, recorded in each replay receipt.

## Reproduction and artifact map

`manifest.json` lists the six selected original formulas, normalized
formulas, CVC5 and Ethos receipts, and deterministic gzip proof archives.
Both compressed and original uncompressed proof hashes are recorded.

    python3 research/sN/max5_optimal_20261103/lower/same_label/verify_bundle.py
    python3 research/sN/max5_optimal_20261103/lower/same_label/verify_bundle.py --replay

The second command needs no SMT solver: it reruns Ethos in temporary
directories and leaves the frozen proof receipts unchanged. The original
model producer and cover hashes are pinned in the manifest. `run.py`
regenerates the six original models; `emit_singleton.py` emits the selected
strengthening of case 277. The initial timeouts for case 277, the alternate
row gauge, and unused stronger variants are preserved as diagnostics.
Timeouts play no role in the exclusion.
