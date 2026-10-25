"""Multi-anchor verifier controls with an exact nonzero anchor re-encoding."""
from fractions import Fraction as Q
from pathlib import Path
import json,hashlib
from overnight_fixed_anchor_verify import check
HERE=Path(__file__).resolve().parent


def main():
    source=json.loads((HERE/'netB_10_6.json').read_text());net=json.loads(json.dumps(source));A=[list(map(Q,row))for row in source['first_layer']];v=[Q(i==2)-Q(i==1)for i in range(5)];jp=A.index(v);jn=A.index([-x for x in v]);a1=A.index([Q(i==1)for i in range(5)]);an1=A.index([-Q(i==1)for i in range(5)]);net['first_layer']+= [[Q(i==2).numerator for i in range(5)],[-Q(i==2).numerator for i in range(5)]];rows=[]
    for raw in source['second_layer']:
        w=list(map(Q,raw))+[Q(0),Q(0)];delta=(w[jp]-w[jn])/2;w[jp]-=delta;w[jn]+=delta;w[a1]-=delta;w[an1]+=delta;w[-2]+=delta;w[-1]-=delta;rows.append(list(map(str,w)))
    assert any(Q(row[-2])for row in rows[2:]);net['second_layer']=rows;path=HERE/'overnight_fixed_anchor_control12_network.json';path.write_text(json.dumps(net,sort_keys=True,indent=2)+'\n');positive=check(path);mutations=[]
    for name in('anchor_pair','comparison_gradient'):
        bad=json.loads(json.dumps(net));j=-1 if name=='anchor_pair'else jp;bad['second_layer'][2][j]=str(Q(bad['second_layer'][2][j])+1);p=HERE/f'overnight_fixed_anchor_control_bad_{name}.json';p.write_text(json.dumps(bad,sort_keys=True,indent=2)+'\n')
        try:check(p)
        except AssertionError as exc:mutations.append({'mutation':name,'rejected':True,'reason':str(exc)})
        else:raise AssertionError('mutation accepted')
    out={'status':'INDEPENDENT_MULTI_ANCHOR_CONTROLS_PASS','exact_reencoding':'σ(x2−x1)−σ(x1−x2)=x2−x1, moved into nonzero coefficients on both anchor pairs','positive_control':positive,'negative_controls':mutations,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_anchor_controls.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
