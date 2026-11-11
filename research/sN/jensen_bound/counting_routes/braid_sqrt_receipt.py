"""Content-bound integer/real square-root parameter bridge receipt."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
stems=['braid_sqrt_final_build','braid_sqrt_check_symbolic']
for stem in stems:
    assert (HERE/(stem+'.exit')).read_text().strip()=='0',stem
log=(HERE/'braid_sqrt_check_symbolic.log').read_text()
checks={}
for name,text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
    axioms=sorted(x.strip() for x in text.split(',') if x.strip())
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(name,axioms)
    checks[name]=axioms
for name in ['braidSqrtMatching_bounds','braidSqrtMatching_eq_floor']:
    assert any(key.endswith('.'+name) for key in checks),name
paths=[Path('MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/Parameters/Sqrt.lean'),
    Path('verification/h2/BraidSqrtParametersCheck.lean'),Path('lean-toolchain'),
    Path('lake-manifest.json'),Path(__file__).resolve().relative_to(ROOT)]
paths += [(HERE/(s+e)).relative_to(ROOT) for s in stems for e in ['.log','.exit']]
receipt={
    'status':'PASS',
    'definition':'braidSqrtMatching n := Nat.sqrt n /400',
    'integer_bounds':'160000<=n implies 1<=braidSqrtMatching n and160000*(braidSqrtMatching n)^2<=n.',
    'real_floor_identity':'For every n:Nat, braidSqrtMatching n=Nat.floor(Real.sqrt(n:Real)/400), with no lower-bound assumption.',
    'proof_method':'Exact natural sqrt lower/upper squares, monotonic squaring, Nat.floor_div_nat and the strict real-square-root floor interval.',
    'scope':'Arithmetic parameter bridge only; the network corollary continues to require the corresponding explicit structural hypothesis.',
    'boundary_scope':'The real-floor identity is proved for every n, including n=0; no concrete Nat.sqrt normalization is part of the audit.',
    'axiom_checks':checks,
    'source_sha256':{str(p):hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}}
(HERE/'braid_sqrt_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: square-root integer bounds and exact real-floor identity; standard axioms.')
