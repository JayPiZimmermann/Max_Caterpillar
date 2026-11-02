"""Content-bound exact integer braid-parameter side-condition receipt."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
stems=['braid_floors_final_build','braid_floors_check']
for stem in stems:
    assert (HERE/(stem+'.exit')).read_text().strip()=='0',stem
log=(HERE/'braid_floors_check.log').read_text()
checks={}
for name,text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
    axioms=sorted(x.strip() for x in text.split(',') if x.strip())
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(name,axioms)
    checks[name]=axioms
assert any(n.endswith('.braid_parameter_bounds') for n in checks)
paths=[Path('MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/Parameters/Floors.lean'),
    Path('verification/h2/BraidParameterFloorsCheck.lean'),Path('lean-toolchain'),
    Path('lake-manifest.json'),Path(__file__).resolve().relative_to(ROOT)]
paths += [(HERE/(s+e)).relative_to(ROOT) for s in stems for e in ['.log','.exit']]
receipt={
    'status':'PASS',
    'scope':'Exact integer parameter definitions k=4q+1, m=n-k, K=m/100 and all floor/positivity side conditions from q>=1 and160000*q^2<=n; no presumed envelope or probability bound.',
    'main_declaration':'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.braid_parameter_bounds',
    'bounds':['k<=5q','2q<=k','k<=n/2','k<=m','m+k=n','80000<=m',
      '4<=K','K<m','100K<=m','m<=200K','n<=400K','n-1<=3(m-1)'],
    'nonvacuity':'n=160000,q=1 gives k=5,m=159995,K=1599, checked in Lean.',
    'axiom_checks':checks,
    'source_sha256':{str(p):hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}}
(HERE/'braid_floors_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: actual integer braid parameters, all floor/positivity bounds, standard axioms.')
