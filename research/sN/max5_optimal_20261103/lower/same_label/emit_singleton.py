"""Add only the elementary singleton-rootless-triple coefficient constraint.

At a top triple with just one singular first hyperplane, which is nonroot,
both positive folds must be effective and have equal absolute coefficients
on that feature. The geometric proof is in notes/max5_exact/allfive_shared_rank.md,
independently audited in notes/max5_exact/shared_rank_audit.md.
No additional odd-vector or face-curvature conditions are used here.
"""
from pathlib import Path
from itertools import combinations
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
OLD=ROOT/'research/sN/frontier5'
sys.path.insert(0,str(OLD))
import max5_exact_three_shared_local as model
z=model.z
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

index=277
cover=OLD/'max5_three_shared_one_each_cover.json'
record=json.loads(cover.read_text())['kinds']['three_roots']['records'][index]
solver,_,meta=model.build('one_each_same',samples='boolean',shared_germs=True,
    rigid=True,supports=record['supports'],coefficient_gauge=True)
roots=[tuple(x) for x in meta['mandatory_roots']]
extras=sorted(tuple(x) for x in record['supports'])
for e in roots: extras.remove(e)
supports=roots+extras
added=[]
for triple in combinations(range(5),3):
    singular=[j for j,s in enumerate(supports) if set(s)<=set(triple)]
    if len(singular)==1 and len(supports[singular[0]])==3:
        j=singular[0];g=z.Real(f'g{j}');h=z.Real(f'h{j}')
        solver.add(g!=0,h!=0,z.Or(g==h,g==-h))
        added.append(dict(triple=triple,row=j))
assert added==[dict(triple=(0,1,3),row=4),dict(triple=(0,1,4),row=6)]
source=HERE/f'case{index}_single.smt2'
source.write_text(solver.to_smt2())
source.with_suffix('.metadata.json').write_text(json.dumps(dict(
    index=index,model_sha256=sha(OLD/'max5_exact_three_shared_local.py'),
    cover_sha256=sha(cover),producer_sha256=sha(__file__),
    source=source.name,source_sha256=sha(source),singleton_rows=added,**meta),indent=2)+'\n')
print(index,len(solver.assertions()),added,flush=True)
