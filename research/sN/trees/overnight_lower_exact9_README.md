# Nine-label exact finite-evaluation gate

25 October 2026. **Complete exact certificate and independent replay passed.**
The all-tree bound is now `binom(N,5)/126` for every `N>=9`, counting only
canonical terms whose original tree has matching number at least four.
See `overnight_lower_nine_bridge.md` for the independently reviewed counting
proof. This is polynomial, not the requested exponential theorem.

The complete domain consists of all rooted, oriented eight-vertex trees
without a perfect matching. Its 3,822 normalized function orbits are covered
by the independent Prüfer/coloured-tree inventory checker. Full permutation
averaging reduces any representation of the symmetric maximum to these orbit
sums. Missing or linear edges have lower support dimension at this arity.

The generic modular matrix has ranks 1,970/1,971. The retained minor uses
1,971 rows and 1,970 ordinary pivot columns plus the target. Two-prime rational
reconstruction proposes 1,852 column relations, each with its own free
coordinate. Reconstruction is not a proof: exact evaluation must check all
relations at all selected points. Their validity on those finite rows is
sufficient; no rational-function identity is assumed.

The exact recurrence is described in `overnight_lower_dp_README.md`.
`overnight_lower_dag_check.py` imports no producer and independently checks
every ordered subset partition and every rooted tree represented in the
compiled graph. It has passed all 1,081,248 summands.

For exact arithmetic there are two separate implementations. The
rational engine reduces fractions throughout the recurrence. The integer
engine takes a common multiple D of every linear denominator and scales a
state with e edges by D^(2e); every division is exact. At the end each engine
produces the unique least common denominator and integer row. The complete
outputs must agree byte for byte. Five- and seven-label independent controls
and every nine-label row have passed. The full campaign has 83 batches,
at most 24 rows per batch, three worker processes, 1000 seconds per arithmetic
process, and a six-hour campaign cap. It checkpoints each completed batch.
An incomplete or timed-out campaign is not a proof; it can resume from the
completed receipts with the same source hashes.

The modular augmented minor is checked by scalar Gaussian elimination in
`overnight_lower_minor_check.cpp`, independently of FLINT's rank proposal.
The exact campaign also checks reduction of every rational row to the original
modular row, with row denominator coprime to the prime. Every gate has
passed. The independent column relations give ordinary rank at most 1,970,
while the augmented minor gives augmented rank at least 1,971.

The main commands, using the recorded deterministic frequency points and
kernel proposal (the prepare step regenerates ignored matrices if needed):

```sh
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_lower_dp.py compile9
research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/overnight_lower_dag_manifest.py
python3 research/sN/trees/overnight_lower_dag_check.py
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_lower_exact9_prepare.py
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_lower_minor_check.py
research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_lower_exact9_run.py
python3 research/sN/trees/overnight_lower_exact9_verify.py
```

Large generated matrices and exact rows are local caches. Their deterministic
inputs, generating source, content hashes and validation receipts are kept;
no unexplained numerical positive or negative result is used. The complete
campaign has 83 passing chunks and 1,971 rows. The separate final streaming
verifier replayed all 3,650,292 rational relation checks, exact modular
reductions and row coverage in 115.19 seconds. This is a finite
computer-assisted proof of a uniform polynomial bound, not the requested
uniform exponential theorem.

The small reference bundle `overnight_lower_exact9_receipts.json` archives
all 83 original receipts and the configuration. It is outside the generated
cache directory so that a fresh checkout regenerates missing rows normally.
Use a separate copy for reproduction: checkers write runtime receipts, whose
byte hashes change between runs. Rational row contents are deterministic.
Compare their canonical uncompressed hashes with the archived receipts.
