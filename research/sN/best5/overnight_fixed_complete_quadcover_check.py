"""Independent finite cover audit and known-network controls."""
from pathlib import Path
from itertools import product,combinations
import hashlib,json,sys
sys.path.insert(0,'/tmp/overnight_fixed_z3')
import z3
from overnight_fixed_anchor_verify import check

HERE=Path(__file__).resolve().parent
out={'status':'PASS','cases':{}}
for mode,majority in [('p2',(0,1)),('p1',(1,2))]:
    representatives=set()
    for assignment in product(range(3),repeat=5):
        counts=[assignment.count(k)for k in range(3)]
        if counts[majority[0]]>counts[majority[1]]:
            a,b=majority;counts[a],counts[b]=counts[b],counts[a]
        representatives.add(tuple(counts))
    assert len(representatives)==12
    out['cases'][mode]=sorted(representatives)
    out['assignments_per_sign']=3**5

# The known K4 construction has every quadruple value zero. It therefore
# belongs to every canonical chosen-zero cover, independently of signs.
source=HERE/'overnight_fixed_complete_decide_control10.smt2'
base=list(z3.parse_smt2_file(str(source)));pairs=list(combinations(range(5),2))
for counts in out['cases']['p2']+out['cases']['p1']:
    solver=z3.SolverFor('QF_LRA');solver.set(timeout=5000);solver.add(*base)
    omitted=0
    for k,count in enumerate(counts):
        for o in range(omitted,omitted+count):
            S=set(range(5))-{o}
            coeff=[int(i in S and j not in S)for i,j in pairs]+[int(i in S)-int(4 in S)for i in range(4)]
            solver.add(z3.Sum([v*z3.Real(f'w{k}_{j}')for j,v in enumerate(coeff)if v])==0)
        omitted+=count
    assert solver.check()==z3.sat,counts
out['known_control_cases']=24
out['global_control']=check(HERE/'overnight_fixed_complete_decide_control10_network.json')
out['control_smt_sha256']=hashlib.sha256(source.read_bytes()).hexdigest()
out['producer_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(HERE/'overnight_fixed_complete_quadcover_check.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
print(json.dumps(out,sort_keys=True))
