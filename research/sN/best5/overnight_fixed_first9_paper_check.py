"""Check the paper's explicit construction against the frozen exact network."""
from fractions import Fraction as Q
import hashlib,json
from pathlib import Path

p=Path('research/sN/best5');tex=(p/'overnight_fixed_first9_paper.tex').read_text();net=json.loads((p/'overnight_fixed_cross_net9_14_simple.json').read_text());table=tex.split('\\lambda_j&a&b&p&c&d&q&r\\\\ \\hline\n')[1].split('\\end{array}')[0];rows=[]
for line in table.splitlines():
    fields=line.strip().removesuffix('\\\\').split('&')
    if len(fields)==8:rows.append([Q(s.strip())for s in fields])
assert len(rows)==12
for paper,actual,out in zip(rows,net['second_layer'][2:],net['output'][2:]):
    lam,L=paper[0],paper[1:];W=list(map(Q,actual[:7]));assert all(Q(x)==0 for x in actual[7:]);j=next(i for i,v in enumerate(L)if v);scale=W[j]/L[j];assert scale>0 and W==[scale*v for v in L] and lam==Q(out)*scale
expected=[Q(-1,2),Q(1,2),Q(0),Q(0),Q(1),Q(1,2),Q(0),Q(1),Q(-1)]
assert list(map(Q,net['second_layer'][0]))==expected
assert list(map(Q,net['second_layer'][1]))==[-v for v in expected]
assert list(map(Q,net['output'][:2]))==[1,-1]
report={'status':'PASS_EXACT_PAPER_CONSTRUCTION_RESCALES_CERTIFIED_NETWORK','rows':12,'first_width':9,'second_width':14,'paper_sha256':hashlib.sha256((p/'overnight_fixed_first9_paper.tex').read_bytes()).hexdigest(),'network_sha256':hashlib.sha256((p/'overnight_fixed_cross_net9_14_simple.json').read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exact positive neuron rescalings and carrier equality; global correctness is inherited from the independent cone certificate for the identical network.'}
(p/'overnight_fixed_first9_paper_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
