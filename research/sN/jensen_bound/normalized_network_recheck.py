#!/usr/bin/env python3
"""Reproduce and bind exact indexed normalization/localization verification.

Use --run to rerun the canonical facade and the two independent expected-type
checks under the project Lean lock. Without it, bind the successful saved gates
and verify every current project source hash before writing the receipt.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
DRIVERS=['verification/h2/NormalizedOrdinaryCheck.lean',
         'verification/h2/NormalizedRestrictionCheck.lean']
PREFIX='MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.'
HEADLINES=[PREFIX+n for n in [
 'ofOrdinary_computes_max','ofOrdinary_translation_normalized','ofOrdinary_exact_direction',
 'eventually_eval_direction','exists_eval_direction','directional_computes_max_of_tied',
 'exists_generic_tied_point','exists_localized_normalized','exists_ordinary_restriction',
 'exists_ordinary_set_restriction','normalizeOuter_computes_max',
 'normalizeOuter_translation_normalized']]

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def closure():
    result={}
    def visit(path):
        rel=str(path.relative_to(ROOT))
        if rel in result:return
        result[rel]=sha(path)
        for mod in re.findall(r'^import\s+([^\s]+)',path.read_text(),re.M):
            child=ROOT/(mod.replace('.','/')+'.lean')
            if child.is_file():visit(child)
    for driver in DRIVERS:visit(ROOT/driver)
    visit(ROOT/'MaxCaterpillar/Frontier/RandomRestriction/NormalizedNetwork.lean')
    return result

def code_only(text):
    result=[];i=0;depth=0;quoted=False
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
        else:result.append(text[i]);i+=1
    return ''.join(result)

before=closure()
checks=[('normalized_network_root_build',
         ['lake','build','MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork']),
        ('normalized_network_ordinary_exact',['lake','env','lean','-j1',DRIVERS[0]]),
        ('normalized_network_restriction_exact',['lake','env','lean','-j1',DRIVERS[1]])]
if '--run' in sys.argv:
    for name,args in checks:
        log=HERE/(name+'.log')
        with log.open('w') as stream:
            proc=subprocess.run([str(ROOT/'scripts/lean_lock.sh'),*args],cwd=ROOT,
                                stdout=stream,stderr=subprocess.STDOUT)
        (HERE/(name+'.exit')).write_text(str(proc.returncode)+'\n')
        if proc.returncode:raise SystemExit(f'FAILED {name}: {proc.returncode}')
logs={}
for name,_ in checks:
    assert (HERE/(name+'.exit')).read_text().strip()=='0',name
    log=HERE/(name+'.log');logs[str(log.relative_to(ROOT))]=sha(log)
text=(HERE/'normalized_network_restriction_exact.log').read_text()
axioms={}
for name in HEADLINES:
    match=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^]]*)\]",text,re.S)
    assert match,name
    deps=sorted(x.strip() for x in match[1].split(',') if x.strip())
    assert set(deps)<={'propext','Classical.choice','Quot.sound'},(name,deps)
    axioms[name]=deps
for filename in before:
    source=code_only((ROOT/filename).read_text())
    assert not re.search(r'\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b',source,re.M),filename
after=closure()
assert before==after,'Sources changed during the gate'
receipt={
 'status':'PASS','module':'MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork',
 'scope':'Actual arbitrary-real-weight/arbitrary-bias ordinary Network N h1 h2 exactMAX_N -> indexed homogeneous skip model for every nonempty selected coordinate set. Same original h1/h2 index types; exact original retained first coefficients; all first and second skip forms zero-sum; output linear sum1; no newfeeding; arbitrary natural indexed support-cost bound. This is a proved reduction, not a final width lower bound.',
 'drivers':DRIVERS,'source_count':len(after),'source_files':after,'logs':logs,
 'headline_axioms':axioms,'forbidden_construct_scan':'PASS',
 'nonvacuity':'Driver instantiates a genuine exact width-(6,5) MAX4 network and restricts to the proper selected input set {0,2}, producing an exact normalized MAX2 model.',
 'semantic_audit':'Independent read-only root_graph_orbits audit found no hidden genericity, normal-form premise, coefficient alphabet, monotonicity assumption, first-row scaling, parallel merging, or index increase. The functional all-ones derivative identity does not assert preservation of the original biased activation patterns; actual parameter construction first uses proved bias removal.',
 'reproduce':'python3 research/sN/jensen_bound/normalized_network_recheck.py --run',
 'toolchain_sha256':sha(ROOT/'lean-toolchain')}
out=HERE/'normalized_network_receipt.json'
out.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(f'PASS {len(after)} current project sources, {len(axioms)} exact axiom audits: {out.relative_to(ROOT)}')
