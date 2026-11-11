"""Exact actual-network chart coverage check, with transitive source audit."""
from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,sys
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'research/sN/zulip_three'
SOURCE='MaxCaterpillar/Fiber/Count65/Paired/Connected.lean'
DRIVER='verification/fiber/Count65PairedConnectedCheck.lean'
PREFIX='MaxCaterpillar.Fiber.Count65.Paired.'
NAMES=[PREFIX+n for n in ['normalized_to_canonical','quotientSector_joined_canonical',
        'isPathConnected_quotientSector','canonicalPairedEndpoint_mem','network_atom_card_cases']]
ALLOWED={'propext','Classical.choice','Quot.sound'}

def closure():
    seen=set();todo=[ROOT/SOURCE,ROOT/DRIVER]
    while todo:
        p=todo.pop()
        if p in seen:continue
        seen.add(p)
        for m in re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M):
            q=ROOT/(m.replace('.','/')+'.lean')
            if q.exists():todo.append(q)
    return seen

def hashes(paths):
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}

def run(args,tag):
    p=subprocess.run([sys.executable,str(OUT/'lean_small_pool.py'),*args],cwd=ROOT,
                     text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/(tag+'.log')).write_text(p.stdout)
    (OUT/(tag+'.exit')).write_text(str(p.returncode)+'\n')
    if p.returncode:raise SystemExit(p.stdout)
    return p.stdout

def main():
    paths=closure();before=hashes(paths)
    target=ROOT/'.lake/build/lib'/SOURCE.replace('.lean','.olean')
    if '--no-build' in sys.argv:
        if ((OUT/'count65_paired_connected.exit').read_text().strip()!='0' or
            target.stat().st_mtime < (ROOT/SOURCE).stat().st_mtime):
            raise SystemExit('Existing owned artifact is stale or failed')
    else:
        run(['lake','env','lean','-j1','-o',str(target),SOURCE],'count65_paired_connected')
    output=run(['lake','env','lean','-j1',DRIVER],'count65_paired_connected_exact')
    axes={name:set(x.strip() for x in ax.split(',') if x.strip()) for name,ax in
          re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output)}
    for name in NAMES:
        if name not in axes or not axes[name]<=ALLOWED:raise SystemExit('Bad axioms: '+name)
    if hashes(paths)!=before:raise SystemExit('Concurrent source edit; rerun check')
    spec=importlib.util.spec_from_file_location('project_verify',ROOT/'scripts/verify.py')
    verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
    for p in paths:
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b',verify.uncomment(p.read_text())):
            raise SystemExit('Forbidden proof construct: '+str(p.relative_to(ROOT)))
    paths.update([ROOT/'lean-toolchain',ROOT/'lake-manifest.json',Path(__file__).resolve()])
    receipt={'status':'PASS','checked_at_utc':datetime.now(timezone.utc).isoformat(),
             'scope':'The complete actual paired sector of the genuine zero-bias symmetry quotient is path connected; every raw completion is handled by actual support extraction and unconditional attachment branches',
             'not_claimed':['Exact number of global symmetry-quotient components'],
             'build_exit':0,'expected_type_exit':0,'nonvacuity':'The canonical identity-code padded network computes Max4 on all real inputs, has zero biases, and belongs to the actual paired quotient sector',
             'axioms':{n:sorted(axes[n]) for n in NAMES},'source_sha256':hashes(paths),
             'receipt_kind':'diagnostic working-tree receipt, not a clean publication gate'}
    dest=OUT/'count65_paired_connected_receipt.json'
    dest.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','hashed_files':len(paths),'axiom_checks':len(NAMES),
                      'receipt':str(dest.relative_to(ROOT))}))

if __name__=='__main__':main()
