#!/usr/bin/env python3
"""Check source-bound evidence for the ordinary MAX5 nine-by-eleven witness."""
from pathlib import Path
import hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def closure(path,found):
    path=path.resolve()
    if path in found:return
    found.add(path)
    for line in path.read_text().splitlines():
        if not line.startswith('import '):continue
        for module in line.split()[1:]:
            if module.startswith(('MaxNN.','MaxCaterpillar.','research.','Verification.')):
                child=ROOT/Path(*module.split('.')).with_suffix('.lean')
                assert child.is_file(),child
                closure(child,found)
def main():
    generated=json.loads((HERE/'generation.json').read_text())
    for rel,h in generated['generated'].items():assert sha(HERE/rel)==h,rel
    assert sha(HERE/'generate.py')==generated['generator_sha256']
    assert sha(ROOT/generated['upstream'])==generated['upstream_sha256']
    assert sha(ROOT/generated['source'])==generated['source_sha256']
    names=['Defs','Weights']+[p.stem for p in sorted(HERE.glob('Cells*.lean'))]+['Identity','Evaluation','Physical','Check']
    for name in names:
        assert (HERE/(name+'.exit')).read_text().strip()=='0',name
        assert 'error:' not in (HERE/(name+'.log')).read_text(),name
    log=(HERE/'Check.log').read_text()
    assert 'sorryAx' not in log and 'Lean.ofReduceBool' not in log
    expected=['network_correct','exists_network','literal_arrays','input_control','deletion_control']
    audits=[]
    for full,raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
        axioms=[x.strip() for x in raw.split(',') if x.strip()]
        assert set(axioms)<= {'propext','Classical.choice','Quot.sound'},(full,axioms)
        audits.append({'declaration':full,'axioms':axioms})
    assert all(any(a['declaration'].endswith('.'+name) for a in audits) for name in expected)
    sources=set();closure(HERE/'Check.lean',sources)
    for source in sources:
        text=source.read_text()
        # Existing comments may discuss forbidden mechanisms; executable
        # declarations are reviewed separately. Reject direct proof stubs.
        assert not re.search(r'(?m)^\s*(?:axiom |sorry\b|admit\b)',text),source
    owned=[p for p in HERE.iterdir() if p.is_file() and p.suffix in ('.lean','.py','.json','.md','.log','.exit') and p.name!='receipt.json']
    controls=[ROOT/generated['source'],ROOT/generated['upstream'],ROOT/'lean-toolchain',ROOT/'lakefile.lean',ROOT/'lake-manifest.json',ROOT/'research/sN/overnight_20261103/lean_pool.py']
    allpaths=set(sources)|set(owned)|set(controls)
    result={'status':'PASS','claim':'Ordinary no-skip MAX5 network with physical widths (9,11), rational weights, zero biases, correct on every real input.',
        'evidence':'Exact Lean types and standard-axiom checks; all new source modules rebuilt. The unchanged imported project closure is source-hashed.',
        'not_claimed':'No new optimality or width improvement; not imported by production root.',
        'axiom_audits':audits,'cells':generated['stats'],'modules':names,
        'project_source_count':len(sources),
        'sources':{str(p.relative_to(ROOT)):sha(p) for p in sorted(allpaths)}}
    (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','project_sources':len(sources),'hashed_files':len(allpaths),'audits':len(audits)}))
if __name__=='__main__':main()
