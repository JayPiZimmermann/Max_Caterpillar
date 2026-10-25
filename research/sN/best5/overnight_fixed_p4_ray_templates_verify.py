"""Independent exact template and K4-domain replay.

Enumerates coefficient flats via all subsets of ten hyperplanes; covers
quadruples by joining two ordered pair lists, not the producer triple loop.
Every allowed template bit is recalculated on every exact fan ray.
"""
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict,Counter
from bisect import bisect_left
from pathlib import Path
import json,time,math,hashlib
import overnight_root9_equations as E
HERE=Path(__file__).resolve().parent


def main():
    started=time.monotonic();E.initialize();a=E.arithmetic;hyper=sorted({a.normalize(a.VALUE[S])[0]for S in a.REL if any(a.VALUE[S])});known={}
    for mask in range(1<<len(hyper)):
        rr=a.rref([h for i,h in enumerate(hyper)if mask>>i&1]);piv=[next(i for i,c in enumerate(row)if c)for row in rr];B=[]
        for free in range(7):
            if free in piv:continue
            v=[Q(0)]*7;v[free]=1
            for p,row in zip(piv,rr):v[p]=-row[free]
            B.append(v)
        zero=sum(1<<i for i,S in enumerate(a.REL)if all(sum(x*y for x,y in zip(a.VALUE[S],v))==0 for v in B));known[zero]=B
    assert len(known)==383 and set(a.BASES)=={z for z,B in known.items()if B}
    zs=sorted(a.BASES);covers=[]
    for z in zs:
        assert a.rref(a.BASES[z])==a.rref(known[z]);forms,cubes,_=a.flat(z);mask=0
        for i,(U,o)in enumerate(a.LOCS[:-1]):
            active=z>>a.RIDX[U]&1
            if o is not None:active=active and z>>a.RIDX[U|{o}]&1
            if active and cubes[U]:mask|=1<<i
        covers.append(mask)
    raw=json.loads((HERE/'overnight_fixed_p4_k4_raytemplates_data.json').read_text());new=json.loads((HERE/'overnight_fixed_p4_k4_raylearn_data.json').read_text());assert raw['flats']==new['flats']==zs;templates=[[(i,Q(c))for i,c in t]for t in raw['templates']+new['templates']];fans={r['flat']:r['rays']for r in map(json.loads,(HERE/'overnight_fixed_p4_flat_rays.jsonl').read_text().splitlines())};allowed=[];rhs=[E.case_data((zs[0],),(1,))[0](i)[1]for i in range(49)];assert all(sum(c*rhs[i]for i,c in t)==1 for t in templates)
    for zi,z in enumerate(zs):
        eq=E.case_data((z,),(1,))[0];rows=[eq(i)[0]for i in range(49)];forms=a.flat(z)[0];fd=math.lcm(*(v.denominator for f in forms for v in f));fi=[[int(v*fd)for v in f]for f in forms];av=[[abs(sum(v*r for v,r in zip(f,ray)))for f in fi]for ray in fans[z]];bits=[0,0]
        for j,t in enumerate(templates):
            c={}
            for i,w in t:
                for k,v in rows[i].items():c[k]=c.get(k,Q(0))+w*v
            cd=math.lcm(*(v.denominator for v in c.values()))if c else 1;ci=[(k,int(cd*v))for k,v in c.items()if v];signs=set()
            for ray in av:
                v=sum(v*ray[k]for k,v in ci)
                if v:signs.add(1 if v>0 else-1)
                if len(signs)==2:break
            if 1 not in signs:bits[0]|=1<<j
            if-1 not in signs:bits[1]|=1<<j
        oldmask=(1<<len(raw['templates']))-1;assert [str(b&oldmask)for b in bits]==raw['allowed_template_bits'][zi]
        for j,tab in enumerate(new['allowed']):assert tuple(bool(b>>(len(raw['templates'])+j)&1)for b in bits)==tuple(tab[zi])
        allowed.append(bits)
    print('EXACT_TEMPLATE_BITS_PASS',len(templates),'seconds',time.monotonic()-started,flush=True)
    pairs=defaultdict(list);oc=Counter()
    for i in range(len(zs)):
        for j in range(i,len(zs)):
            m=covers[i]|covers[j];pairs[m].append((i,j));oc[m]+=1 if i==j else 2
    full=(1<<25)-1;assert full not in pairs;triples=sum(n for mask,n in oc.items()for c in covers if mask|c==full);assert triples==1302
    quads=cases=excluded=remaining=ordered4=0;signs=list(product((0,1),repeat=4));oldsurvivors={tuple(r['flats']):r['sign_mask']for r in map(json.loads,(HERE/'overnight_fixed_p4_k4_raytemplate_survivors.jsonl').read_text().splitlines())};oldseen={};remaining_path=HERE/'overnight_fixed_p4_k4_rayverified_survivors.jsonl'
    with remaining_path.open('w')as out:
      for ml,left in pairs.items():
       for mr,right in pairs.items():
        if ml|mr!=full:continue
        ordered4+=oc[ml]*oc[mr]
        for i,j in left:
          for k,l in right[bisect_left(right,(j,-1)):]:
            quad=tuple(zs[v]for v in(i,j,k,l));quads+=1;openmask=oldopen=0
            for si,ss in enumerate(signs):
                common=allowed[i][ss[0]]&allowed[j][ss[1]]&allowed[k][ss[2]]&allowed[l][ss[3]];cases+=1
                if not(common&oldmask):oldopen|=1<<si
                if common:excluded+=1
                else:remaining+=1;openmask|=1<<si
            if oldopen:assert quad not in oldseen;oldseen[quad]=oldopen
            if openmask:out.write(json.dumps({'flats':quad,'sign_mask':openmask},separators=(',',':'))+'\n')
    assert oldseen==oldsurvivors;assert quads==(ordered4+6*triples)//24==296861 and cases==16*quads;report={'status':'INDEPENDENT_EXACT_P4_RAY_TEMPLATE_PREPASS_PASS','relevant_hyperplanes':len(hyper),'nonzero_flats':len(zs),'templates':len(templates),'ordered_covering_quadruples':ordered4,'covering_quadruples':quads,'sign_cases':cases,'exact_template_exclusions':excluded,'remaining_cases':remaining,'seconds':time.monotonic()-started,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'survivors_sha256':hashlib.sha256(remaining_path.read_bytes()).hexdigest(),'scope':'Complete unbounded real-parameter necessary flat/sign domain. Remaining cases are unresolved; no K4 lower bound.'};(HERE/'overnight_fixed_p4_ray_templates_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
