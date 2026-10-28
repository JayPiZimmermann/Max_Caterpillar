"""Exact finite boundary control: matches 16 ray planes, fails globally.
The all-scale identity is proved in overnight_fixed_rayplane_obstruction.md.
"""
import hashlib
import itertools
import json
from fractions import Fraction as Q
from pathlib import Path


def main():
    terms={}
    def add(row,c):
        key=tuple(row);terms[key]=terms.get(key,Q(0))+c
    L=[(0,1,1,0,0,0),(1,-1,0,0,0,0),(0,0,1,0,0,0)]
    K=[(0,0,0,0,1,1),(0,0,0,1,-1,0),(0,0,0,0,0,1)];eps=(1,1,-1)
    for i,j in itertools.product(range(3),repeat=2):add([a-b for a,b in zip(L[i],K[j])],Q(eps[i]*eps[j]))
    h1=(-1,1,1,0,0,0);h2=(0,0,0,-1,1,1)
    for r,s,c in [(-1,0,Q(1,2)),(0,1,Q(1,2)),(-1,1,Q(1,2)),(0,0,Q(-1,2))]:
        g=(-1,1,r,1,-1,s)
        add(g,-c);add([a-b for a,b in zip(g,h1)],c)
        add([a+b for a,b in zip(g,h2)],c);add([a-b+cc for a,b,cc in zip(g,h1,h2)],-c)
    terms={g:c for g,c in terms.items() if c and any(g)}
    net={"N":5,"first_layer":[[-1,1,0,0,0],[-1,0,1,0,0],[0,1,-1,0,0],[-1,0,0,1,0],[-1,0,0,0,1],[0,0,0,1,-1],[1,0,0,0,0],[-1,0,0,0,0]],
         "second_layer":[[0,0,0,1,0,0,1,-1],[0,0,0,-1,0,0,-1,1]]+[list(g)+[0,0] for g in terms],
         "output":["1","-1"]+[str(c) for c in terms.values()],
         "scope":"Boundary control only; not a representation of max5 on all inputs"}
    def evaluate(x):
        first=[max(sum(Q(a)*b for a,b in zip(row,x)),0) for row in net["first_layer"]]
        return sum(Q(out)*max(sum(Q(a)*b for a,b in zip(row,first)),0) for row,out in zip(net["second_layer"],net["output"]))
    rays=[(0,1),(1,1),(1,0),(0,-1)];scales=[Q(0),Q(1,2),Q(1),Q(2),Q(3)];count=0
    for r,s,u,v in itertools.product(range(4),range(4),scales,scales):
        point=(Q(0),u*rays[r][0],u*rays[r][1],v*rays[s][0],v*rays[s][1])
        assert evaluate(point)==max(point);count+=1
    bad=(0,-2,-3,1,-3);actual=evaluate(bad);assert actual==Q(3,2) and max(bad)==1
    path=Path("overnight_fixed_rayplane_control_net.json");path.write_text(json.dumps(net,indent=2)+"\n")
    result={"status":"EXACT_RAYPLANE_CONTROL_PASS_GLOBAL_IDENTITY_FALSE","grid_controls":count,
        "hidden_widths":[8,len(net["second_layer"])],"counterexample":{"x":bad,"actual":str(actual),"target":"1"},
        "network_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"All-scale ray-plane equality has an algebraic proof in the accompanying note; finite grid is an exact implementation control"}
    Path("overnight_fixed_rayplane_control.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
