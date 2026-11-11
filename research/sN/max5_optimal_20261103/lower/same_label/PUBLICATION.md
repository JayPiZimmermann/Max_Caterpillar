# Selected six-case publication closure

The exact file list is `publication_paths.txt`; `publication_files.json`
records hashes and separates selected artifacts, runtime dependencies and
background mathematics. It excludes diagnostic timeouts, unused stronger
models, unselected CPC proofs and all ongoing degeneration experiments.
The original six-proof manifest is unchanged.

From a clean checkout containing that file list, Python's standard library
is sufficient to check the frozen arithmetic proofs:

    python3 research/sN/max5_optimal_20261103/lower/same_label/verify_bundle.py --replay

The imported local-MAX4 one-root/two-nonroot lemma has a separate compact
288-case aggregate proof, included in this file closure. Its fresh replay
also passed and can be repeated without changing any upstream receipt:

    python3 research/sN/max5_optimal_20261103/lower/same_label/verify_local4_background.py

This command restores the compressed proofs into temporary directories,
checks every source and proof hash, and independently checks each proof of
false against the corresponding normalized source. It does not trust a
saved solver verdict. The fresh replay of all six selected proofs passed.

The upstream arithmetic auditor downloads Ethos 0.2.5 from the release URL
in `research/sN/best5/overnight_root_complete_ethos_manifest.json`. It verifies
the archive SHA256 `5d9c41e53d97d918ccd682b0012032ba26994d964309328cddb4a20df116e296`
and executable SHA256
`939147a0a40b6ba78dc32dfd2f8d9fe9686154057773c023984ebe0b0168e3d1`.
The same manifest supplies all 35 CPC signature URLs at the pinned
`cvc5-1.4.2` tag and verifies each file's SHA256. Files are cached under the
system temporary directory. Neither an existing `/tmp` installation nor
an SMT solver is needed for replay. The unrelated old SMT instance and
proof named by that dependency manifest are not read by this replay.

Regenerating the formulas additionally needs the Python Z3 bindings; the
recorded run used version 5.3.3. Regenerating CPC proofs needs Python cvc5
1.4.2. The existing import fallbacks name historical temporary directories,
but ordinary installed packages are also found through the usual Python
module path. `run.py --mode emit` emits the original six formulas, and
`emit_singleton.py` emits the selected strengthening of case 277. A fresh
producer run should be compared with the frozen source hashes before
replacing any artifact.

Arithmetic replay does not prove the network-to-model bridge. Its inputs
are the prior first-width-nine result, the local one-core MAX4
classification, the positive-two-core MAX4 theorem with at most three
singular first hyperplanes, and the elementary one-line MAX3 lemma.
The local model audit explains normalization, opposite and proportional
rows, strict unique-contact signs and directional derivatives. The new
short minimal-root cover is in `audit/MINIMAL_COVER.md` and its executable
replay; it avoids the older 193-to-387 support-cover pipeline and its
three-comparator budget. Case 277's only added clauses are proved in
`audit/SINGLETON_AUDIT.md`. The listed background notes make these prior
mathematical dependencies available for review; this package does not
claim they have all been formalized as Lean network theorems.

The finite conclusion excludes the same-label three-shared-contact sector
when exactly the three mandatory root planes occur among seven invariant
physical rows. The further 381 old support classes, and other contact
sectors, are not excluded by these six certificates.

`midpoint_cover.py` separately freezes the exact 225-case count for the
new midpoint argument being assembled by the parent task. Its receipt
proves the finite support predicate only; it is not an arithmetic proof
of those exclusions and is kept distinct from the six-proof manifest.
