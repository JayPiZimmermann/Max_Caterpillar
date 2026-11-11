#!/usr/bin/env python3
"""Fresh owned-source closure and exact scalar/actual checks for general rows."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

root=Path(__file__).resolve().parents[2]
os.chdir(root)
base=Path('MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching')
sources=[base/p for p in ['Parameters/GeneralRows.lean','Parameters/SmallFalling.lean',
    'Parameters/GeneralRowsCoverage.lean','Parameters/GeneralRowsEnvelope.lean','GeneralRows.lean']]
check=Path('verification/h2/GeneralRowsCheck.lean')
out=Path('research/sN/jensen_bound')
allowed={'propext','Classical.choice','Quot.sound'}
ns='MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.'
expected={ns+'Parameters.'+p for p in ['general_row_parameter_bounds','descFactorial_three_lower',
    'descFactorial_four_lower','general_row_coverage','general_row_envelope']}
expected|={ns+p for p in ['conditional_general_rows_of_tail','conditional_general_rows']}
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
closure={}
def visit(p):
    p=Path(p)
    if str(p) in closure:return
    closure[str(p)]=digest(p)
    for line in re.findall(r'^import ([^\n]+)',p.read_text(),re.M):
        for name in line.split():
            if name.startswith('MaxCaterpillar.'):
                visit(Path(name.replace('.','/')+'.lean'))
for p in sources+[check]:visit(p)
receipt={'sources':{str(p):digest(p) for p in sources},'check':str(check),
    'check_sha256':digest(check),'producer':str(Path(__file__).resolve().relative_to(root)),
    'producer_sha256':digest(__file__),'project_source_closure':closure,
    'allowed_axioms':sorted(allowed),'steps':[],
    'scope':'Actual normalized network finite general-row corollary; local H(4q+1,q) remains explicit.'}
owned={p.with_suffix(suffix) for p in sources for suffix in ['.olean','.ilean']}
def mirror(original,overlay,relative=Path()):
    overlay.mkdir(parents=True,exist_ok=True)
    if not original.is_dir():return
    for child in original.iterdir():
        rel=relative/child.name
        if rel in owned:continue
        if child.is_dir() and any(rel in p.parents for p in owned):
            mirror(child,overlay/child.name,rel)
        else:
            (overlay/child.name).symlink_to(child.resolve(),target_is_directory=child.is_dir())
search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
lean=subprocess.check_output(['lake','env','which','lean'],text=True).strip()
with tempfile.TemporaryDirectory(prefix='max_caterpillar_general_rows_') as directory:
    overlay=Path(directory)
    mirror(root/'.lake/build/lib',overlay)
    env=dict(os.environ,LEAN_PATH=str(overlay)+':'+search)
    commands=[]
    for p in sources:
        target=overlay/p.with_suffix('.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        commands.append((str(p.relative_to(base).with_suffix('')).replace('/','_'),
            [lean,'-j1','-o',str(target),str(p)]))
    commands.append(('exact_check',[lean,'-j1',str(check)]))
    for name,command in commands:
        log=out/('general_rows_'+name+'.log')
        with log.open('w') as handle:
            result=subprocess.run(command,env=env,stdout=handle,stderr=subprocess.STDOUT)
        text=log.read_text();print(text,end='',flush=True)
        axioms={decl:[a.strip() for a in body.split(',') if a.strip()]
            for decl,body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)}
        receipt['steps'].append({'name':name,'command':command,'exit_code':result.returncode,
            'axioms':axioms,'log':str(log),'log_sha256':digest(log)})
        if result.returncode:break
receipt['sources_unchanged']=all(digest(p)==h for p,h in receipt['sources'].items())
receipt['closure_unchanged']=all(digest(p)==h for p,h in closure.items())
receipt['check_unchanged']=digest(check)==receipt['check_sha256']
receipt['owned_lexical_passed']=all(not re.search(r'\b(?:sorry|admit|native_decide|axiom)\b',p.read_text()) for p in sources+[check])
printed=set().union(*(set(s['axioms']) for s in receipt['steps']))
receipt['axiom_audit_passed']=expected<=printed and all(set(ax)<=allowed for s in receipt['steps'] for ax in s['axioms'].values())
receipt['success']=(len(receipt['steps'])==len(sources)+1 and all(s['exit_code']==0 for s in receipt['steps'])
    and all(receipt[k] for k in ['sources_unchanged','closure_unchanged','check_unchanged','owned_lexical_passed','axiom_audit_passed']))
(out/'general_rows_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
raise SystemExit(0 if receipt['success'] else 1)
