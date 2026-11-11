"""Content-bound receipt for the separate generic finite-index leaf."""
from pathlib import Path
import ast,hashlib,json,re
R=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
checks={}
for stem in ['finite_index_build','finite_index_check']:
 assert (D/(stem+'.exit')).read_text().strip()=='0'
 log=(D/(stem+'.log')).read_text();assert 'error:' not in log
 reports={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)}
 assert len(reports)>0 and all(set(a)<=allowed for a in reports.values())
 checks[stem]={'exit':0,'log_sha256':sha(D/(stem+'.log')),'axioms':reports}
p=R/'research/sN/jensen_bound/star_obstruction/star_obstruction_receipt.py'
node=next(n for n in ast.parse(p.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='strip_comments')
ns={};exec(compile(ast.Module(body=[node],type_ignores=[]),str(p),'exec'),ns)
found={};todo=[D/'FiniteIndex.lean',D/'FiniteIndexCheck.lean']
while todo:
 p=todo.pop()
 if p in found:continue
 found[p]=sha(p)
 assert not re.search(r'\b(sorry|admit|native_decide|sorryAx)\b|\bLean\.ofReduceBool\b|(?m:^\s*(?:private\s+)?axiom\s+)',ns['strip_comments'](p.read_text()))
 for line in p.read_text().splitlines():
  if line.strip().startswith('import '):
   for mod in line.strip()[7:].split():
    q=R/Path(*mod.split('.')).with_suffix('.lean')
    if q.exists():todo.append(q)
# Do not mutate the previous structural receipt or its closure.
old=json.loads((D/'receipt.json').read_text())
for p,h in old['project_import_source_hashes'].items():assert sha(R/p)==h
for p,h in old['control_hashes'].items():assert sha(R/p)==h
artifact=R/'.lake/build/lib'/D.relative_to(R)/'FiniteIndex.olean';assert artifact.exists()
j={'success':True,'scope':'Actual arbitrary finite-index network constructor and exact inner/eval/support/normalization/signed-interaction reindexing. Research only.',
 'no_nonempty_index_hypotheses':True,'expanded_type_and_empty_family_nonvacuity_checks':True,
 'checks':checks,'source_hashes':{str(p.relative_to(R)):h for p,h in sorted(found.items())},
 'control_hashes':{str(p.relative_to(R)):sha(p) for p in [Path(__file__).resolve(),D/'FiniteIndex.md']},
 'artifact':{'path':str(artifact.relative_to(R)),'sha256':sha(artifact)},
 'prior_structural_receipt_sha256':sha(D/'receipt.json'),'prior_structural_closure_unchanged':True,
 'lean_toolchain':(R/'lean-toolchain').read_text().strip()}
(D/'finite_index_receipt.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps({'success':True,'checks':len(checks),'sources':len(found),'axiom_reports':sum(len(x['axioms']) for x in checks.values())}))
