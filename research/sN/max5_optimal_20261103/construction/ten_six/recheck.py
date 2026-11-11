"""Recheck the physical MAX5 (10,6) theorem and exact witness correspondence.

No Lean source is generated. The checker rebuilds the two hand-written leaves,
checks the literal expected formula and transitive axiom output, compares the
rational arrays against the earlier independently certified JSON witness, and
hashes all repository-owned transitive imports. External mathlib/toolchain
versions are pinned by the root project files.
"""
import ast, hashlib, json, re, subprocess
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def rational_ast(node):
    if isinstance(node, ast.List): return [rational_ast(x) for x in node.elts]
    if isinstance(node, ast.Constant) and isinstance(node.value, int): return Fraction(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub): return -rational_ast(node.operand)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        return rational_ast(node.left)/rational_ast(node.right)
    raise AssertionError(ast.dump(node))


def read_weights(text, name):
    block = text.split('def '+name+' :',1)[1].split(':=',1)[1].split('\n\n',1)[0].strip()
    return rational_ast(ast.parse(block.replace('![','['),mode='eval').body)


def closure(path, found):
    if path in found: return
    found.add(path)
    for line in path.read_text().splitlines():
        if line.startswith('import '):
            for module in line[7:].split():
                child=ROOT/(module.replace('.','/')+'.lean')
                if child.is_file(): closure(child,found)


def main():
    source=HERE/'Network.lean'
    witness=ROOT/'research/sN/best5/netB_10_6.json'
    data=json.loads(witness.read_text())
    def fractions(v):
        return [fractions(x) for x in v] if isinstance(v,list) else Fraction(v)
    for lean,key in [('firstWeights','first_layer'),('secondWeights','second_layer'),('outputWeights','output')]:
        assert read_weights(source.read_text(),lean)==fractions(data[key]),key
    checks=[]
    for name in ['Network','Check']:
        file=HERE/(name+'.lean')
        artifact=ROOT/'.lake/build/lib'/file.relative_to(ROOT).with_suffix('.olean')
        artifact.parent.mkdir(parents=True,exist_ok=True)
        cmd=['python3','research/sN/overnight_20261103/lean_pool.py','lake','env','lean',
             '-o',str(artifact.relative_to(ROOT)),str(file.relative_to(ROOT))]
        log=HERE/(name.lower()+'_check.log')
        with log.open('w') as out:
            result=subprocess.run(cmd,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
        (HERE/(name.lower()+'_check.exit')).write_text(str(result.returncode)+'\n')
        assert result.returncode==0,log
        output=log.read_text()
        assert 'sorryAx' not in output and 'Lean.ofReduceBool' not in output,log
        audits=re.findall(r"depends on axioms: \[([^\]]*)\]",output)
        assert len(audits)==2,(name,audits)
        for audit in audits:
            assert set(filter(None,map(str.strip,audit.split(',')))) <= {'propext','Classical.choice','Quot.sound'}
        checks.append({'module':str(file.relative_to(ROOT)),'command':cmd,'exit':0,'axiom_audits':audits})
    paths=set()
    closure(HERE/'Check.lean',paths)
    for path in [witness,Path(__file__),ROOT/'lean-toolchain',ROOT/'lake-manifest.json',ROOT/'lakefile.lean',
                 HERE/'network_check.log',HERE/'check_check.log',HERE/'network_check.exit',HERE/'check_check.exit']:
        paths.add(path)
    receipt={'status':'PASS','scope':'Ordinary no-skip rational zero-bias MAX5 network of physical widths (10,6).',
        'new_width_claim':False,'literal_array_comparison':'exact match with independently certified netB_10_6.json',
        'declarations':['MaxCaterpillar.MaxFiveTenSix.net_eval','MaxCaterpillar.MaxFiveTenSix.exists_network',
            'MaxCaterpillar.MaxFiveTenSix.Check.literal_formula','MaxCaterpillar.MaxFiveTenSix.Check.exact_type'],
        'checks':checks,'source_hashes':{str(p.relative_to(ROOT)):sha(p) for p in sorted(paths)},
        'publication_status':'Research leaf checked against local source closure; committed closure review belongs to publication gate.'}
    (HERE/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','files_hashed':len(paths),'declarations':receipt['declarations']}),flush=True)


if __name__=='__main__':main()
