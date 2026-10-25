"""Independent exact replay and coverage count for a bounded facet batch.

Only standard library. Recomputes every new template bit, checks every
closed proof tree, then compares against the frozen full-domain residual.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import product
from functools import lru_cache
import json,math,time,hashlib
import overnight_root9_equations as E
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();E.initialize();fans={r['flat']:r['rays']for r in map(json.loads,(HERE/'overnight_fixed_p4_flat_rays.jsonl').read_text().splitlines())};zsall=sorted(fans);raw=json.loads((HERE/'overnight_fixed_p4_facet_batch_templates.json').read_text())['templates'];old=[]
    for name in('overnight_fixed_p4_k4_raytemplates_data.json','overnight_fixed_p4_k4_raylearn_data.json'):old+=json.loads((HERE/name).read_text())['templates']
    assert raw[:140]==old and len(old)==140;templates=[[(i,Q(c))for i,c in t]for t in raw];rhs=[E.case_data((zsall[0],),(1,))[0](i)[1]for i in range(49)];assert all(sum(c*rhs[i]for i,c in t)==1 for t in templates)
    @lru_cache(None)
    def block(z):
        forms=E.arithmetic.flat(z)[0];vals=[[abs(sum(a*b for a,b in zip(f,r)))for f in forms]for r in fans[z]];eq=E.case_data((z,),(1,))[0];rows=[eq(i)[0]for i in range(49)];return forms,vals,rows
    bits={}
    for z in zsall:
        forms,vals,rows=block(z);den=math.lcm(*(x.denominator for v in vals for x in v));integer=[[int(x*den)for x in v]for v in vals];allowed=[0,0]
        for ti,t in enumerate(templates[140:]):
            co={}
            for i,c in t:
                for j,v in rows[i].items():co[j]=co.get(j,Q(0))+c*v
            cd=math.lcm(*(v.denominator for v in co.values()))if co else 1;ci=[(j,int(v*cd))for j,v in co.items()if v];seen=set()
            for ray in integer:
                value=sum(v*ray[j]for j,v in ci)
                if value:seen.add(1 if value>0 else-1)
                if len(seen)==2:break
            if 1 not in seen:allowed[0]|=1<<ti
            if-1 not in seen:allowed[1]|=1<<ti
        bits[z]=allowed
    residual={tuple(r['flats']):r['sign_mask']for r in map(json.loads,(HERE/'overnight_fixed_p4_k4_rayverified_survivors.jsonl').read_text().splitlines())};assert sum(m.bit_count()for m in residual.values())==10952;proved={};totals={'nodes':0,'branches':0,'leaves':0}
    def check(node,zs,ds,allowed,counts):
        counts['nodes']+=1
        if node[0]=='cone':
            assert len(node)==2;t=[(i,Q(c))for i,c in node[1]];assert len({i for i,c in t})==len(t)and all(0<=i<49 for i,c in t);assert sum(c*rhs[i]for i,c in t)>0
            for k,z in enumerate(zs):
                fs,vals,rows=block(z);co={}
                for i,c in t:
                    for j,v in rows[i].items():co[j]=co.get(j,Q(0))+c*v
                for j in allowed[k]:assert ds[k]*sum(c*vals[j][t]for t,c in co.items())<=0
            counts['leaves']+=1;return
        assert node[0]=='triangle'and len(node)==7;k,inds,cs=node[1:4];cs=list(map(Q,cs));assert 0<=k<4 and len(inds)==len(set(inds))==len(cs)==3 and all(c>0 for c in cs);fs,vals,_=block(zs[k]);f=[fs[j]for j in inds];assert any(all(sum(s*c*v[t]for s,c,v in zip(sgn,cs,f))==0 for t in range(len(f[0])))for sgn in product((1,-1),repeat=3));slacks=[[sum(c*v[j]for c,j in zip(cs,inds))-2*cs[t]*v[inds[t]]for t in range(3)]for v in vals];assert all(s>=0 for row in slacks for s in row);counts['branches']+=1
        for t in range(3):
            aa=list(allowed);aa[k]=tuple(j for j in allowed[k]if slacks[j][t]==0);check(node[4+t],zs,ds,tuple(aa),counts)
    for line in(HERE/'overnight_fixed_p4_facet_batch_proofs.jsonl').read_text().splitlines():
        p=json.loads(line);zs=tuple(p['flats']);ds=tuple(p['signs']);assert len(ds)==4 and all(d in(-1,1)for d in ds);sc=sum((d<0)<<(3-i)for i,d in enumerate(ds));assert residual[zs]>>sc&1 and(zs,ds)not in proved;counts={'nodes':0,'branches':0,'leaves':0};check(p['tree'],zs,ds,tuple(tuple(range(len(fans[z])))for z in zs),counts);assert counts==p['counts'];proved[zs,ds]=counts
        for k,v in counts.items():totals[k]+=v
    template_closed=tree_closed=remaining=0;outpath=HERE/'overnight_fixed_p4_facet_batch_remaining.jsonl'
    with outpath.open('w')as out:
      for zs,mask in residual.items():
        openmask=0
        for si,ds in enumerate(product((1,-1),repeat=4)):
            if not(mask>>si&1):continue
            common=(1<<(len(templates)-140))-1
            for z,d in zip(zs,ds):common&=bits[z][int(d<0)]
            if common:template_closed+=1
            elif(zs,ds)in proved:tree_closed+=1
            else:remaining+=1;openmask|=1<<si
        if openmask:out.write(json.dumps({'flats':zs,'sign_mask':openmask},separators=(',',':'))+'\n')
    out={'status':'INDEPENDENT_EXACT_BOUNDED_FACET_BATCH_PASS','checked_trees':len(proved),'tree_counts':totals,'templates':len(templates),'input_cases':10952,'new_template_exclusions':template_closed,'further_tree_exclusions':tree_closed,'remaining_cases':remaining,'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'remaining_sha256':hashlib.sha256(outpath.read_bytes()).hexdigest(),'scope':'Exact partial coverage of the frozen full-domain residual; no whole-domain K4 exclusion while remaining_cases is positive.'};(HERE/'overnight_fixed_p4_facet_batch_check.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__':main()
