"""Standalone exact P4 K4 exclusion: stdlib only, no LP solver.

Independently rebuilds the full coefficient-flat and cover domain, verifies
all ray fans, every rational template, all closed facet trees, and complete
quadruple/sign coverage. Input data are untrusted until these checks pass.
"""
from fractions import Fraction as Q
from itertools import product,combinations
from collections import defaultdict,Counter
from bisect import bisect_left
from pathlib import Path
import json,time,math,hashlib
import overnight_root9_equations as E
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();E.initialize();a=E.arithmetic;cp=HERE/'overnight_fixed_p4_k4_certificate.json';cert=json.loads(cp.read_text());hyper=sorted({a.normalize(a.VALUE[S])[0]for S in a.REL if any(a.VALUE[S])});known={}
    for mask in range(1<<len(hyper)):
        rr=a.rref([h for i,h in enumerate(hyper)if mask>>i&1]);piv=[next(i for i,c in enumerate(row)if c)for row in rr];B=[]
        for free in range(7):
            if free in piv:continue
            v=[Q(0)]*7;v[free]=1
            for p,row in zip(piv,rr):v[p]=-row[free]
            B.append(v)
        zero=sum(1<<i for i,S in enumerate(a.REL)if all(sum(x*y for x,y in zip(a.VALUE[S],v))==0 for v in B));known[zero]=B
    assert len(known)==383 and set(a.BASES)=={z for z,B in known.items()if B};zs=sorted(a.BASES);fans={}
    for line in(HERE/'overnight_fixed_p4_flat_rays.jsonl').read_text().splitlines():
        rec=json.loads(line);assert rec['flat']not in fans;fans[rec['flat']]=rec
    assert set(fans)==set(zs);covers=[];blocks={};total_rays=total_subsets=0
    for z in zs:
        assert a.rref(a.BASES[z])==a.rref(known[z]);forms,cubes,_=a.flat(z);d=len(a.BASES[z]);m=len(forms);rec=fans[z];assert(rec['dimension'],rec['forms'])==(d,m)and len(a.rref(forms))==d;seen=set();covered=set()
        for raw in rec['rays']:
            r=tuple(raw);assert len(r)==d and any(r)and all(type(v)is int for v in r)and math.gcd(*r)==1 and next(v for v in r if v)>0 and r not in seen;seen.add(r);zeros=[j for j,f in enumerate(forms)if sum(v*t for v,t in zip(f,r))==0];assert len(a.rref([forms[j]for j in zeros]))==d-1
            for subset in combinations(zeros,d-1):covered.add(subset)
        assert len(covered)==math.comb(m,d-1);total_rays+=len(seen);total_subsets+=len(covered);mask=0
        for i,(U,o)in enumerate(a.LOCS[:-1]):
            active=z>>a.RIDX[U]&1
            if o is not None:active=active and z>>a.RIDX[U|{o}]&1
            if active and cubes[U]:mask|=1<<i
        covers.append(mask);vals=[[abs(sum(v*t for v,t in zip(f,r)))for f in forms]for r in rec['rays']];eq=E.case_data((z,),(1,))[0];rows=[eq(i)[0]for i in range(49)];blocks[z]=forms,vals,rows
    templates=[[(i,Q(c))for i,c in t]for t in cert['templates']];rhs=[E.case_data((zs[0],),(1,))[0](i)[1]for i in range(49)]
    for t in templates:assert len({i for i,c in t})==len(t)and all(type(i)is int and 0<=i<49 for i,c in t)and sum(c*rhs[i]for i,c in t)==1
    allowed=[]
    for z in zs:
        forms,vals,rows=blocks[z];den=math.lcm(*(v.denominator for ray in vals for v in ray));integer=[[int(v*den)for v in ray]for ray in vals];bits=[0,0]
        for ti,t in enumerate(templates):
            co={}
            for i,c in t:
                for j,v in rows[i].items():co[j]=co.get(j,Q(0))+c*v
            cd=math.lcm(*(v.denominator for v in co.values()))if co else 1;ci=[(j,int(v*cd))for j,v in co.items()if v];signs=set()
            for ray in integer:
                value=sum(v*ray[j]for j,v in ci)
                if value:signs.add(1 if value>0 else-1)
                if len(signs)==2:break
            if 1 not in signs:bits[0]|=1<<ti
            if-1 not in signs:bits[1]|=1<<ti
        allowed.append(bits)
    trees={};tree_counts=Counter()
    def check(node,flatids,ds,keep,counts):
        counts['nodes']+=1
        if node[0]=='cone':
            assert len(node)==2;t=[(i,Q(c))for i,c in node[1]];assert len({i for i,c in t})==len(t)and all(0<=i<49 for i,c in t)and sum(c*rhs[i]for i,c in t)>0
            for k,z in enumerate(flatids):
                forms,vals,rows=blocks[z];co={}
                for i,c in t:
                    for j,v in rows[i].items():co[j]=co.get(j,Q(0))+c*v
                for j in keep[k]:assert ds[k]*sum(c*vals[j][t]for t,c in co.items())<=0
            counts['leaves']+=1;return
        assert node[0]=='triangle'and len(node)==7;k,inds,cs=node[1:4];cs=list(map(Q,cs));assert 0<=k<4 and len(inds)==len(set(inds))==len(cs)==3 and all(c>0 for c in cs);forms,vals,_=blocks[flatids[k]];fs=[forms[j]for j in inds];assert any(all(sum(s*c*f[t]for s,c,f in zip(sgn,cs,fs))==0 for t in range(len(fs[0])))for sgn in product((1,-1),repeat=3));slacks=[[sum(c*v[j]for c,j in zip(cs,inds))-2*cs[t]*v[inds[t]]for t in range(3)]for v in vals];assert all(s>=0 for row in slacks for s in row);counts['branches']+=1
        for t in range(3):
            new=list(keep);new[k]=tuple(j for j in keep[k]if slacks[j][t]==0);check(node[4+t],flatids,ds,tuple(new),counts)
    for p in cert['trees']:
        flatids=tuple(p['flats']);ds=tuple(p['signs']);assert len(flatids)==len(ds)==4 and list(flatids)==sorted(flatids)and all(z in blocks for z in flatids)and all(d in(-1,1)for d in ds);assert(flatids,ds)not in trees;counts=Counter();check(p['tree'],flatids,ds,tuple(tuple(range(len(fans[z]['rays'])))for z in flatids),counts);assert dict(counts)==p['counts'];trees[flatids,ds]=counts;tree_counts.update(counts)
    pairs=defaultdict(list);oc=Counter()
    for i in range(len(zs)):
        for j in range(i,len(zs)):
            mask=covers[i]|covers[j];pairs[mask].append((i,j));oc[mask]+=1 if i==j else 2
    full=(1<<25)-1;assert full not in pairs;ordered3=sum(n for mask,n in oc.items()for c in covers if mask|c==full);assert ordered3==1302;ordered4=quads=cases=template_closed=tree_closed=0;used=set();signs=list(product((0,1),repeat=4))
    for ml,left in pairs.items():
      for mr,right in pairs.items():
        if ml|mr!=full:continue
        ordered4+=oc[ml]*oc[mr]
        for i,j in left:
          for k,l in right[bisect_left(right,(j,-1)):]:
            quads+=1;flatids=tuple(zs[v]for v in(i,j,k,l))
            for ss in signs:
                cases+=1;common=allowed[i][ss[0]]&allowed[j][ss[1]]&allowed[k][ss[2]]&allowed[l][ss[3]]
                if common:template_closed+=1
                else:
                    ds=tuple(1 if s==0 else-1 for s in ss);key=flatids,ds;assert key in trees,key;used.add(key);tree_closed+=1
    assert quads==(ordered4+6*ordered3)//24==296861 and cases==16*quads==4749776;assert used==set(trees)and tree_closed==20;assert template_closed+tree_closed==cases
    deps=['overnight_root9_equations.py','overnight_root9_inventory.json','overnight_fixed_bowtie_verify.py','overnight_fixed_cross_net9_17.json','overnight_fixed_p4_flat_rays.jsonl','overnight_fixed_p4_k4_certificate.json'];report={'status':'INDEPENDENT_EXACT_P4_FOUR_FREE_TERMS_EXCLUDED','relevant_hyperplanes':len(hyper),'flats_including_zero':len(known),'arrangement_rays':total_rays,'covered_normal_subsets':total_subsets,'covering_quadruples':quads,'sign_cases':cases,'templates':len(templates),'template_exclusions':template_closed,'closed_facet_cases':tree_closed,'facet_tree_counts':dict(tree_counts),'core_lower_bound':5,'fixed_second_hidden_layer_lower_bound':7,'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'hashes':{f:hashlib.sha256((HERE/f).read_bytes()).hexdigest()for f in deps},'scope':'Certified finite real-parameter exclusion for the fixed seven-feature P4 span modulo arbitrary linear remainder. Established two-carrier bridge gives h2>=7 for that fixed nine-row first hidden layer. Not an unrestricted h1=9 theorem; not Lean; upper bound14 remains unmatched.'};(HERE/'overnight_fixed_p4_k4_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
