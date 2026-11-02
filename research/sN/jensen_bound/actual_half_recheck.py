#!/usr/bin/env python3
"""Exact actual-network half-restriction gate; --run reproduces its checks."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
DRIVER='verification/h2/ActualHalfRestrictionCheck.lean'
MODULE='MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction'
PREFIX='MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction.'
HEADLINES=[PREFIX+n for n in ['exists_half_support_fourth_moment','actual_first_width_pos',
 'moment_controls_count','count_budget_of_moment','regularized_moment_budget',
 'exists_actual_model','exists_actual_half_model']]
WEIGHTED='MaxCaterpillar/Frontier/RandomRestriction/WeightedRestriction.lean'
FROZEN_WEIGHTED='81a7957930d0399f2952c4b2a9ac431ed517df823d96fa96b563c7efed5ba05a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def closure():
 result={}
 def visit(p):
  rel=str(p.relative_to(ROOT))
  if rel in result:return
  result[rel]=sha(p)
  for name in re.findall(r'^import\s+([^\s]+)',p.read_text(),re.M):
   q=ROOT/(name.replace('.','/')+'.lean')
   if q.is_file():visit(q)
 visit(ROOT/DRIVER);visit(ROOT/(MODULE.replace('.','/')+'.lean'))
 return result

def code_only(text):
 out=[];i=0;depth=0;quoted=False
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;i+=2
   elif text.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif quoted:
   if text[i]=='\\':i+=2
   elif text[i]=='"':quoted=False;i+=1
   else:i+=1
  elif text.startswith('/-',i):depth=1;i+=2
  elif text.startswith('--',i):
   j=text.find('\n',i);i=len(text) if j<0 else j
  elif text[i]=='"':quoted=True;i+=1
  else:out.append(text[i]);i+=1
 return ''.join(out)

before=closure();assert before[WEIGHTED]==FROZEN_WEIGHTED
checks=[('actual_half_root_build',['lake','build',MODULE]),
        ('actual_half_exact',['lake','env','lean','-j1',DRIVER])]
if '--run' in sys.argv:
 for name,args in checks:
  with (HERE/(name+'.log')).open('w') as stream:
   p=subprocess.run([str(ROOT/'scripts/lean_lock.sh'),*args],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
  (HERE/(name+'.exit')).write_text(str(p.returncode)+'\n')
  if p.returncode:raise SystemExit(f'FAILED {name}: {p.returncode}')
logs={}
for name,_ in checks:
 assert (HERE/(name+'.exit')).read_text().strip()=='0',name
 p=HERE/(name+'.log');logs[str(p.relative_to(ROOT))]=sha(p)
text=(HERE/'actual_half_exact.log').read_text();axioms={}
for name in HEADLINES:
 m=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^]]*)\]",text,re.S);assert m,name
 deps=sorted(x.strip() for x in m[1].split(',') if x.strip())
 assert set(deps)<={'propext','Classical.choice','Quot.sound'},(name,deps)
 axioms[name]=deps
for path in before:
 code=code_only((ROOT/path).read_text())
 assert not re.search(r'\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b',code,re.M),path
after=closure();assert before==after,'Source changed during gate'
receipt={'status':'PASS','module':MODULE,'driver':DRIVER,'source_count':len(after),
 'source_files':after,'logs':logs,'headline_axioms':axioms,'forbidden_construct_scan':'PASS',
 'scope':'Ordinary arbitrary-real-weight/arbitrary-bias exact MAX_N network, N>=1040: one selected set S of size floor(N/2) and one normalized indexed skip model computing MAX_floor(N/2) on ALL real inputs, with original Fin h1/Fin h2 and simultaneous4*actualFourthMoment<=81*h1,4*actualNonBraidCount<=h1,4*max(actualFourthMoment,1)<=81*h1. No parity, model, support-budget or first-width-positivity premise is assumed; h1>=1 is derived from exactness.',
 'parity':'First2n coordinates are embedded injectively. A support is pulled back only if wholly inside; supports touching an omitted odd coordinate become empty, never smaller intersections. No input identification occurs.',
 'nonvacuity':'Independent driver applies the stronger generic positive-n theorem to an actual odd-input MAX3 network and gets one normalized MAX1 model at the original widths(4,3).',
 'weighted_source_sha256':FROZEN_WEIGHTED,
 'export_scope_precision':'The half headline exports exactness, normalization and simultaneous statistics. It intentionally drops upstream explicit coefficient-lineage/feeding clauses. Those remain available from exists_ordinary_set_restriction; the proof constructs its model at the actual selected S.',
 'remaining_separate_step':'The additional cap1000*h1<=N^3 implies240*M<=n(n-1)(n-2) using the existing scalar half_restriction_count_budget lemma; that cap is not part of this headline.',
 'reproduce':'python3 research/sN/jensen_bound/actual_half_recheck.py --run',
 'toolchain_sha256':sha(ROOT/'lean-toolchain')}
p=HERE/'actual_half_receipt.json';p.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(f'PASS {len(after)} current project sources, {len(axioms)} standard-only axiom audits: {p.relative_to(ROOT)}')
