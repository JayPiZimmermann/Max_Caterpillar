"""Content-bound exact audit for the actual growing-arity neuron envelope."""
from pathlib import Path
import hashlib, importlib.util, json, re
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
MODULE='MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventModel'
DRIVER=Path('verification/h2/GrowingActualModelCheck.lean')
for stem in ['actual_rank_build','actual_model_build','good_model_build','actual_model_check']:
 assert (HERE/(stem+'.exit')).read_text().strip()=='0',stem
log=(HERE/'actual_model_check.log').read_text()
assert not re.search(r'error:|sorryAx|Lean\.ofReduceBool',log)
checks={}
for name,text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
 axioms=sorted(x.strip() for x in text.split(',') if x.strip())
 assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(name,axioms)
 checks[name]=axioms
for name in re.findall(r"'([^']+)' does not depend on any axioms",log):checks[name]=[]
assert len(checks)==22,len(checks)
paths=set();stack=[MODULE]
while stack:
 name=stack.pop();p=Path(*name.split('.')).with_suffix('.lean')
 if p in paths or not (ROOT/p).is_file():continue
 paths.add(p)
 for line in (ROOT/p).read_text().splitlines():
  if line.startswith('import '):stack.extend(line.split()[1:])
project_sources=sorted(paths)
spec=importlib.util.spec_from_file_location('max_verify_source_scan',ROOT/'scripts/verify.py')
scanner=importlib.util.module_from_spec(spec);spec.loader.exec_module(scanner)
for p in project_sources+[DRIVER]:
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',scanner.uncomment((ROOT/p).read_text())),str(p)
paths.update([DRIVER,Path('lean-toolchain'),Path('lake-manifest.json'),Path('lakefile.lean')])
for stem in ['actual_rank_build','actual_model_build','good_model_build','actual_model_check']:
 for ext in ['.log','.exit']:paths.add((HERE/(stem+ext)).relative_to(ROOT))
paths.add(Path(__file__).resolve().relative_to(ROOT))
receipt=dict(status='PASS',module=MODULE,exact_driver=str(DRIVER),
 scope='Actual arbitrary-real network original second preactivation, original-coordinate gap point, literal uniform full/tail/rank permutation sample, and actual clean condition, for arbitrary selected arity k.',
 main_declaration='GrowingMatching.actualNeuron_fraction_le',
 hypotheses=['net : NormalizedNetwork (m+k) h1 h2','net.TranslationNormalized','m>=2','K>0','CommonGapScale net T'],
 conclusion='P(actual clean second survival AND Qgood AND selected ambient q-matching) <= (k)_(2q)/(m+k)_(2q) * c^(-q) * exp(c*k*(m+k-1)), c=7K/[24m(m-1)]',
 no_assumed_rank_probability_or_count=True,
 bridges=['Actual inner-zero vs actual restricted effective row at same scale.',
  'Actual recording-fiber fair-coin rank and full signed coefficients.',
  'Actual all-graph partialmatching Laplace estimate.',
  'Actual selected q-matchings retaining q! and exponential-series cancellation.',
  'Actual induced-tail deletion, uniformly in selected/tail correlations.',
  'Actual counted A/B/C good event implies actual clean original rows.'],
 scale_theorem='exists_common_gap_threshold derives a common actual positive scale from arbitrary coefficient arrays, with no MAX or normalization premise.',
 expected_type_checks=['Expanded actual-network event-fraction bound and rate.',
  'Expanded original-array common-threshold existence.',
  'Literal counted all-support good event implies actual cleanliness.',
  'Zero selected arity and positive matching has literal empty actual event.'],
 axiom_checks=checks,project_source_closure_count=len(project_sources),
 commands=['lake build '+MODULE,'lake env lean -j1 '+str(DRIVER)],
 source_commit=None,working_tree_content_bound=True,
 excluded_unverified_route='BERNOULLI.md remains a separate paper candidate until its association/conditioning/model bridge is formally verified; this receipt does not certify that route.',
 source_sha256={str(p):hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(HERE/'growing_actual_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: actual growing-arity envelope,22 standard-axiom audits,',len(project_sources),'project sources')
