"""Exact content-bound audit of Bernoulli actual-neuron conditional cost."""
from pathlib import Path
import hashlib,importlib.util,json,re
ROOT=Path(__file__).resolve().parents[5];HERE=Path(__file__).resolve().parent
MODULE='MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.ActualModel'
DRIVER=Path('verification/h2/BernoulliActualModelCheck.lean')
for stem in ['bernoulli_actual_build','bernoulli_actual_check']:
 assert (HERE/(stem+'.exit')).read_text().strip()=='0',stem
log=(HERE/'bernoulli_actual_check.log').read_text()
assert not re.search(r'error:|sorryAx|Lean\.ofReduceBool',log)
checks={}
for name,text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
 axioms=sorted(x.strip() for x in text.split(',') if x.strip())
 assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(name,axioms)
 checks[name]=axioms
for name in re.findall(r"'([^']+)' does not depend on any axioms",log):checks[name]=[]
assert len(checks)==11,len(checks)
paths=set();stack=[MODULE]
while stack:
 name=stack.pop();p=Path(*name.split('.')).with_suffix('.lean')
 if p in paths or not(ROOT/p).is_file():continue
 paths.add(p)
 for line in(ROOT/p).read_text().splitlines():
  if line.startswith('import '):stack.extend(line.split()[1:])
closure=sorted(paths)
spec=importlib.util.spec_from_file_location('max_verify_source_scan',ROOT/'scripts/verify.py')
scanner=importlib.util.module_from_spec(spec);spec.loader.exec_module(scanner)
for p in closure+[DRIVER]:
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',scanner.uncomment((ROOT/p).read_text())),str(p)
paths.update([DRIVER,Path('lean-toolchain'),Path('lake-manifest.json'),Path('lakefile.lean')])
for stem in ['bernoulli_actual_build','bernoulli_actual_check']:
 for ext in ['.log','.exit']:paths.add((HERE/(stem+ext)).relative_to(ROOT))
paths.add(Path(__file__).resolve().relative_to(ROOT))
receipt=dict(status='PASS',module=MODULE,exact_driver=str(DRIVER),
 scope='Actual original real-network second survival jointly with the literal ActualClean, Qgood and ordinary selected q-matching events; Bernoulli-selected labels with genuine variable-tail permutation means.',
 conditional_inputs='p in[0,1], positive-mass actual downward selected-set event D, selected size cap b and tail dimension at least2 on D; common actual generic scale. Canonical admissibleSets and Sampling threshold discharge these in the final assembly.',
 main_declaration='Bernoulli.actualNeuronMean_le',
 conclusion='actual conditional neuron mean <= (p^2/c0)^q exp(c0*b*(n-1)), c0=7K/(24n^2)',
 derived_bridges=['Conditional selected matching event via weighted FKG/Harris.',
 'Ordinary q-edge-set counting retains q!; exponential-series cancellation.',
 'Uniform actual complement-edge moment under recorded matching-fiber survival.',
 'Rate weakening BEFORE inserting possibly negative ordinary edge-deletion lower bound.',
 'Joint clean/survival mean, not survival conditional on Good.',
 'Same original-coordinate point and original Fin h2 neuron index.'],
 no_assumed_rank_or_probability_bound=True,
 checks=['Expanded actual event meaning.', 'Expanded c0 and conditional original-neuron mean type.',
 'Conditional q! graph count without conditioning-rarity loss.', 'q=0 selected matching event is genuinely all subsets.'],
 axiom_checks=checks,project_source_closure_count=len(closure),
 commands=['lake build '+MODULE,'lake env lean -j1 '+str(DRIVER)],
 source_commit=None,working_tree_content_bound=True,
 publication_status='Scoped exact verification only; full actual-network sqrt theorem and its explicit open H remain a separate final gate.',
 source_sha256={str(p):hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)})
(HERE/'bernoulli_actual_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: actual Bernoulli conditional neuron cost,11 standard axioms checks,',len(closure),'project sources')
