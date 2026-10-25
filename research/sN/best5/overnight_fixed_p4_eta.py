"""Targeted exact extension of the known four-free-term maximum identity.

Only its one comparison argument eta is varied, over the seven P4 features.
A contradiction at finitely many exact inputs excludes this ansatz globally;
a feasible candidate would still need the independent full-cone verifier.
"""
from fractions import Fraction as Q
from itertools import product
import hashlib,json
from pathlib import Path


def relu(x):return max(Q(0),x)
def features(p):
    u,v,s,t=p;return list(map(relu,(u,v,v-u,s,t,s-t,v-t)))
def control(p):
    u,v,s,t=p;z=list(map(relu,(u,u-v,-v,v,s,-t,t,s-t)));coef=(0,-1,1,-1,0,-1,1,1);return sum(a*b for a,b in zip(z,coef))
def condition(p):
    a,b,c,d=map(relu,p);S=a+b;T=c+d;D=abs(a-b);E=abs(c-d);k=(T-S)/2;needed=max(a,b,c,d)-(S+max(D,E))/2
    if not k:assert needed==0;return None
    if k>0:
        if needed==0:return('le',Q(0))
        if needed==k:return('ge',k)
        assert 0<needed<k;return('eq',needed)
    if needed==0:return('le',k)
    if needed==k:return('ge',Q(0))
    assert k<needed<0;return('eq',k-needed)


def main():
    records=[];pivots={};contradiction=None;count=0
    points=sorted(product(range(-3,4),repeat=4),key=lambda p:(sum(abs(v)for v in p),p))
    for p in points:
        p=tuple(map(Q,p));test=condition(p)
        if test is None:continue
        kind,value=test;eta=control(p);assert(kind=='eq'and eta==value)or(kind=='le'and eta<=value)or(kind=='ge'and eta>=value);count+=1
        if kind!='eq':continue
        row=features(p)+[value];index=len(records);records.append({'point':list(map(str,p)),'features':list(map(str,row[:7])),'required_eta':str(value)});combo={index:Q(1)}
        for col,(old,comb)in sorted(pivots.items()):
            c=row[col]
            if not c:continue
            row=[a-c*b for a,b in zip(row,old)]
            for j,v in comb.items():combo[j]=combo.get(j,Q(0))-c*v
        col=next((j for j,v in enumerate(row[:7])if v),None)
        if col is None:
            if row[7]:contradiction={j:v/row[7]for j,v in combo.items()if v};break
            continue
        c=row[col];row=[v/c for v in row];combo={j:v/c for j,v in combo.items()if v};pivots[col]=(row,combo)
    assert contradiction is not None
    cert=[dict(records[j],multiplier=str(c))for j,c in sorted(contradiction.items())]
    assert all(sum(Q(r['multiplier'])*Q(r['features'][i])for r in cert)==0 for i in range(7));assert sum(Q(r['multiplier'])*Q(r['required_eta'])for r in cert)==1
    report={'status':'EXACT_P4_LINEAR_ETA_EXTENSION_IMPOSSIBLE','model':'Known four-free-term max identity with its sole eta argument replaced by an arbitrary linear form in the seven fixed P4 features. Other outer forms unchanged.','certificate':cert,'required_equalities_examined':len(records),'known_fixed10_positive_controls':count,'scope':'Ansatz exclusion only; not a lower bound against arbitrary four-free-term representations on P4.','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};out=Path('research/sN/best5/overnight_fixed_p4_eta.json');out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
