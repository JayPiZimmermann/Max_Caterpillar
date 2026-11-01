"""Exact global-kink positive control using the certified (10,6) network."""
import hashlib
import itertools
import json
from fractions import Fraction as Q
from pathlib import Path


def canonical(v):
    c=next((x for x in v if x),None)
    return (None,Q(0)) if c is None else (tuple(x/c for x in v),abs(c))


def main():
    net=json.loads(Path("netB_10_6.json").read_text())
    W=[[Q(x) for x in row] for row in net["second_layer"]];d=list(map(Q,net["output"]))
    order=[0,3,1,2,4,6,7,5]
    w=[[row[i] for i in order] for row in W[2:]]
    r=[(1,0,1,0),(1,1,0,0),(0,1,0,0),(0,0,0,1),(0,0,1,1)]
    cones=[(r[0],r[1]),(r[1],r[2]),(r[3],r[4]),(r[4],r[0])]
    values=[(1,1),(1,1),(0,0),(0,1)]
    checked=0;nonzero=0
    for i,j in itertools.product(range(4),repeat=2):
        sums={}
        for weight,out in zip(w,d[2:]):
            v=tuple(sum(a*b for a,b in zip(weight[:4],ray)) for ray in cones[i])+tuple(sum(a*b for a,b in zip(weight[4:],ray)) for ray in cones[j])
            if min(v)<0<max(v):
                normal,scale=canonical(v);sums[normal]=sums.get(normal,Q(0))+out*scale
        target=values[i]+tuple(-x for x in values[j])
        if min(target)<0<max(target):
            normal,scale=canonical(tuple(map(Q,target)));sums[normal]=sums.get(normal,Q(0))-scale;nonzero+=1
        assert not any(sums.values()),(i,j,sums)
        checked+=1
    for S in [S for k in range(1,5) for S in itertools.combinations(range(5),k)]:
        x=[Q(int(i in S)) for i in range(5)];u,v,s,t=[x[i]-x[1] for i in (0,2,3,4)]
        features=[max(u,0),max(v,0),max(u-v,0),max(-v,0),max(s,0),max(t,0),max(s-t,0),max(-t,0)]
        result=features[0]+sum(out*max(sum(a*b for a,b in zip(weight,features)),0) for weight,out in zip(w,d[2:]))
        assert result==1-x[1]
    result={"status":"EXACT_GLOBAL_KINK_DICTIONARY_CONTROL_PASS","product_cones":checked,"target_kink_cones":nonzero,"rays":30,
            "network_sha256":hashlib.sha256(Path("netB_10_6.json").read_bytes()).hexdigest(),
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_dictionary_control.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
