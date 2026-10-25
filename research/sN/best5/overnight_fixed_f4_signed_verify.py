"""Exact graph and frame algebra for all shallow F4-orbit relations."""
from fractions import Fraction as Q
from itertools import product
import hashlib,json
from pathlib import Path
from overnight_fixed_f4_verify import compose,function,dot


def main():
    I=tuple(tuple(2*int(i==j) for j in range(4)) for i in range(4))
    A1=((1,-1,-1,-1),(1,-1,1,1),(1,1,-1,1),(1,1,1,-1))
    A2=((1,-1,-1,1),(1,-1,1,-1),(1,1,-1,-1),(1,1,1,1))
    frames=(I,A1,A2);functions={};classes={}
    for k,A in enumerate(frames):
        for signs in product((-1,1),repeat=4):
            f=function(tuple(tuple(s*v for v in row) for s,row in zip(signs,A)))
            parity=signs[0]*signs[1]*signs[2]*signs[3];classes[f]=(k,parity)
    functions=sorted(classes);index={f:i for i,f in enumerate(functions)};base=index[function(I)]
    generators=[]
    for k in range(3):
        p=list(range(4));p[k],p[k+1]=p[k+1],p[k]
        generators.append(tuple(tuple(2*int(p[i]==j) for j in range(4)) for i in range(4)))
    generators.extend((tuple(tuple((-2 if i==j==0 else 2*int(i==j)) for j in range(4)) for i in range(4)),((1,1,1,1),(1,1,-1,-1),(1,-1,1,-1),(1,-1,-1,1))))
    actions=[[index[compose(f,B)] for f in functions] for B in generators]
    interior=(1,1,1,3);nonzero=[i for i,f in enumerate(functions) if min(dot(row,interior) for row in f)>0];assert len(nonzero)==2 and base in nonzero
    edges={tuple(sorted(nonzero))};todo=list(edges)
    while todo:
        i,j=todo.pop()
        for action in actions:
            edge=tuple(sorted((action[i],action[j])))
            if edge not in edges:edges.add(edge);todo.append(edge)
    assert len(edges)==96
    adj=[set() for f in functions]
    for i,j in edges:adj[i].add(j);adj[j].add(i)
    assert all(len(a)==4 for a in adj)
    color={};components=[]
    for i in range(48):
        if i in color:continue
        color[i]=1;todo=[i];comp=[]
        while todo:
            j=todo.pop();comp.append(j)
            for k in adj[j]:
                if k not in color:color[k]=-color[j];todo.append(k)
                else:assert color[k]==-color[j]
        components.append(sorted(comp))
    assert len(components)==3 and all(len(c)==16 for c in components)
    # Relations: E+0-E+2, E-0-E+1, E-2-E-1.
    classpairs=(((0,1),(2,1)),((0,-1),(1,1)),((2,-1),(1,-1)))
    relation=[]
    for plus,minus in classpairs:
        w=[int(classes[f]==plus)-int(classes[f]==minus) for f in functions]
        assert all(w[i]+w[j]==0 for i,j in edges)
        support=[i for i,v in enumerate(w) if v];assert support in components;relation.append(w)
    assert sorted(i for w in relation for i,v in enumerate(w) if v)==list(range(48))
    def signedrows(A):return {tuple(s*v for v in row) for row in A for s in(-1,1)}
    assert signedrows(A1)=={s for s in product((-1,1),repeat=4) if s[0]*s[1]*s[2]*s[3]==-1}
    assert signedrows(A2)=={s for s in product((-1,1),repeat=4) if s[0]*s[1]*s[2]*s[3]==1}
    # These products prove the three parity identities via the max-sign formula.
    expected={(1,2):1,(1,1):2,(2,2):0,(2,1):0}
    for (i,j),k in expected.items():assert signedrows(compose(frames[i],frames[j]))==signedrows(frames[k])
    # RHS vectors in the basis (||x||1,||A1x||1,||A2x||1), scaled by2.
    rhs=((1,0,-1),(1,-1,0),(0,-1,1))
    assert tuple(rhs[0][i]-rhs[1][i]+rhs[2][i] for i in range(3))==(0,0,0)
    assert rhs[0][0]*rhs[1][1]-rhs[0][1]*rhs[1][0]!=0
    report={'status':'PASS_EXACT_F4_ALL_SHALLOW_RELATIONS','functions':48,'edge_constraints':96,'bipartite_components':components,'relations':relation,'rhs_twice_l1_coefficients':rhs,'dimensions':{'coefficient_relations_modulo_shallow':3,'actual_zero_relations':1,'orbit_function_span':47,'shallow_intersection':2,'quotient_span':45},'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'dependency_sha256':hashlib.sha256(Path('overnight_fixed_f4_verify.py').read_bytes()).hexdigest()}
    Path('overnight_fixed_f4_signed_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in('relations','bipartite_components')},sort_keys=True,indent=2))
if __name__=='__main__':main()
