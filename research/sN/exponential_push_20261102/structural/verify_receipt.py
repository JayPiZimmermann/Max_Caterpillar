"""Hash and inspect already-run research-only kernel checks; no Lean execution.

Rebuild each owned leaf/driver with lake env lean -j1 under lean_small_pool.py.
This receipt does not claim a clean-commit/publication gate or H(13,3).
"""
from pathlib import Path
import ast,hashlib,json,re
R=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
allowed={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
# Reuse the existing audited lexical comment/string stripper, without executing
# the old receipt module or changing any frozen control file.
p=R/'research/sN/jensen_bound/star_obstruction/star_obstruction_receipt.py'
tree=ast.parse(p.read_text());strip=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='strip_comments')
ns={};exec(compile(ast.Module(body=[strip],type_ignores=[]),str(p),'exec'),ns);strip_comments=ns['strip_comments']
checks={}
for stem in ['circuit_deletion','circuit_deletion_artifact','circuit_deletion_check','actual_braid_artifact','actual_braid_graph','actual_braid_check']:
 assert (D/(stem+'.exit')).read_text().strip()=='0',stem
 log=(D/(stem+'.log')).read_text();assert 'error:' not in log,stem
 reports={name:[a.strip() for a in axs.split(',') if a.strip()] for name,axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)}
 assert reports and all(set(axs)<=allowed for axs in reports.values()),stem
 checks[stem]={'exit':0,'log_sha256':sha(D/(stem+'.log')),'axioms':reports}
starts=[D/x for x in ['CircuitDeletion.lean','CircuitDeletionCheck.lean','ActualBraid.lean','ActualBraidGraph.lean','ActualBraidCheck.lean']]
found={};todo=list(starts)
while todo:
 p=todo.pop()
 if p in found:continue
 found[p]=sha(p)
 for line in p.read_text().splitlines():
  if line.strip().startswith('import '):
   for mod in line.strip()[7:].split():
    q=R/Path(*mod.split('.')).with_suffix('.lean')
    if q.exists():todo.append(q)
for p in found:
 assert not re.search(r'\b(sorry|admit|native_decide|sorryAx)\b|\bLean\.ofReduceBool\b|(?m:^\s*(?:private\s+)?axiom\s+)',strip_comments(p.read_text())),str(p)
artifacts={}
for name in ['CircuitDeletion','ActualBraid','ActualBraidGraph']:
 p=R/'.lake/build/lib'/D.relative_to(R)/(name+'.olean');assert p.exists();artifacts[str(p.relative_to(R))]=sha(p)
receipt={'success':True,'scope':'Research-only: exact generic circuit identity; arbitrary-N actual normalized braid canonicalization; signed interaction graph bridge. No H(k,3), SC2, or exponential theorem is claimed.',
 'checks':checks,'artifacts':artifacts,'project_import_source_hashes':{str(p.relative_to(R)):h for p,h in sorted(found.items())},
 'control_hashes':{str(p.relative_to(R)):sha(p) for p in [Path(__file__).resolve(),D/'README.md']},
 'toolchain':(R/'lean-toolchain').read_text().strip(),'status':'kernel checked and independently exact-type/nonvacuity checked; isolated research, not production-integrated'}
(D/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'success':True,'checks':len(checks),'project_sources':len(found),'axiom_reports':sum(len(x['axioms']) for x in checks.values())}))
