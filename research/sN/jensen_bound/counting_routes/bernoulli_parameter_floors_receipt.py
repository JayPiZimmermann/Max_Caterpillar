"""Content-bound Bernoulli parameter floors and exact algebra receipt."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
stems=['bernoulli_parameter_defs_final_build','bernoulli_parameter_floors_algebra_build',
       'bernoulli_parameter_floors_check_final']
for stem in stems:
    assert (HERE/(stem+'.exit')).read_text().strip()=='0',stem
log=(HERE/'bernoulli_parameter_floors_check_final.log').read_text()
checks={}
for name,text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
    axioms=sorted(x.strip() for x in text.split(',') if x.strip())
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(name,axioms)
    checks[name]=axioms
for name in ['parameter_bounds','probability_mul_total','probability_sq_mul_total',
             'mean_sq','alpha_sq','rankCount_eq_floor']:
    assert any(key.endswith('.'+name) for key in checks),name
base=Path('MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/Bernoulli/Parameters')
paths=[base/'Defs.lean',base/'Floors.lean',Path('verification/h2/BernoulliParameterFloorsCheck.lean'),
       Path('lean-toolchain'),Path('lake-manifest.json'),Path(__file__).resolve().relative_to(ROOT)]
paths += [(HERE/(s+e)).relative_to(ROOT) for s in stems for e in ['.log','.exit']]
receipt={
    'status':'PASS',
    'hypotheses':'d:Nat,1<=d,n:Nat,10^10*d^2<=n.',
    'scope':'Exact scalar size, positivity and floor conditions for the literal Bernoulli definitions. No probability, support-budget, neuron-envelope, structural hypothesis or network lower bound is assumed or proved here.',
    'main_declaration':'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.parameter_bounds',
    'main_type':'ParameterBounds n d',
    'bounds':['n,d,sqrt(n)>0','mu>=100','0<p<=1/1000<=1','q>=1','mu/9<=q<=mu/8',
      'k0<=3mu/5','cap<=2mu','cap<=n','m0+cap=n','n<=2m0','m0>=400',
      'K>=4','100K<=m0','delta*n/2<=K<=delta*n','0<delta<=1/1000','k0<=cap'],
    'exact_identities':['p*n=mu','p^2*n=alpha^2','mu^2=alpha^2*n',
      'alpha^2=1/(10^6*d^2)','K=Nat.floor((n:Real)/(1000*(d:Real)^2))'],
    'verification':'Symbolic expected-type and axiom audit only; no concrete numeric square-root evaluation.',
    'axiom_checks':checks,
    'source_sha256':{str(p):hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}}
(HERE/'bernoulli_parameter_floors_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: literal Bernoulli parameter floors, size bounds and exact algebra; standard axioms.')
