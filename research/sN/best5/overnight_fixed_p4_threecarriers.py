"""Targeted five-unit ansatz: three natural carriers, two arbitrary corrections.

No coefficient dictionary. Exact first-cell curvature compatibility proposes
continuous affine families for the two negative preactivations. Every candidate
must separately pass the full-domain network checker before being a result.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations,product
import json,time,signal,hashlib
from overnight_fixed_bowtie_verify import rref
from overnight_fixed_cross_verify import check as globalcheck
HERE=Path(__file__).resolve().parent


def aff(rows):
    rr=rref(rows)
    return None if any(not any(r[:-1])and r[-1]for r in rr)else rr


def main():
    start=time.monotonic();net=json.loads((HERE/'overnight_fixed_cross_net9_14_simple.json').read_text());A=[[Q(x)for x in r]for r in net['first_layer'][:7]];W=[[Q(x)for x in r[:7]]for r in net['second_layer'][2:]];D=list(map(Q,net['output'][2:]));plus=[[Q(x)for x in r]for r in [[1,0,0,-1,0,0,0],[1,0,0,0,-1,0,0],[0,0,0,0,0,1,-1]]];cells={}
    for p in permutations(range(5)):
        rank={v:i for i,v in enumerate(p)};act=[row if rank[next(i for i,x in enumerate(row)if x>0)]<rank[next(i for i,x in enumerate(row)if x<0)]else[Q(0)]*5 for row in A];key=tuple(any(row)for row in act);cell=cells.setdefault(key,{'active':act,'sets':set()});cell['sets'].update(tuple(sorted(p[:t]))for t in range(1,5))
    for key,cell in cells.items():
        curv={};act=cell['active']
        for w,d in zip(W+plus,[-d for d in D]+[Q(1)]*3):
            g=tuple(sum(w[j]*act[j][i]for j in range(7))for i in range(5));vs=[sum(g[j]for j in S)for S in cell['sets']]
            if min(vs)<0<max(vs):
                sc=next(x for x in g if x);normal=tuple(x/sc for x in g);curv[normal]=curv.get(normal,Q(0))+d*abs(sc)
        cell['curvature']=[(g,c)for g,c in sorted(curv.items())if c];assert len(cell['curvature'])<=2 and all(c>0 for g,c in cell['curvature'])
    double=[c for c in cells.values()if len(c['curvature'])==2];single=[c for c in cells.values()if len(c['curvature'])==1];assert len(double)==2 and len(single)==12
    def fixedrows(cell,k,g,c):return [[Q(0)]*(7*k)+[cell['active'][j][i]for j in range(7)]+[Q(0)]*(7*(1-k))+[c*g[i]]for i in range(5)]
    first=double[0];families={aff(fixedrows(first,0,*first['curvature'][0])+fixedrows(first,1,*first['curvature'][1]))};counts=[]
    second=double[1];new=set()
    for fam in families:
        for p in((0,1),(1,0)):
            for s,t in product((1,-1),repeat=2):
                g,c=second['curvature'][p[0]];h,d=second['curvature'][p[1]];rr=aff(list(fam)+fixedrows(second,0,g,s*c)+fixedrows(second,1,h,t*d))
                if rr is not None:new.add(rr)
    families=new;counts.append(len(families));print('DOUBLE',len(families),[len(f)for f in families],flush=True);signal.signal(signal.SIGALRM,lambda *_:(_ for _ in()).throw(TimeoutError('90 second budget')));signal.alarm(90);complete=True
    try:
      for ci,cell in enumerate(sorted(single,key=lambda c:len(rref(c['active'])),reverse=True)):
        g,c=cell['curvature'][0];pivot=next(i for i,x in enumerate(g)if x);opts=[]
        for k in range(2):
            for s in(1,-1):opts.append(fixedrows(cell,k,g,s*c))
        # Both units proportional to the one surviving normal. Signed sum
        # of their normal amplitudes is c; nonnegativity is checked later.
        base=[]
        for k in range(2):
            for i in range(5):base.append([Q(0)]*(7*k)+[cell['active'][j][i]-g[i]*cell['active'][j][pivot]for j in range(7)]+[Q(0)]*(7*(1-k))+[Q(0)])
        for s,t in product((1,-1),repeat=2):opts.append(base+[[s*cell['active'][j][pivot]for j in range(7)]+[t*cell['active'][j][pivot]for j in range(7)]+[c]])
        new=set()
        for fam in families:
            for eq in opts:
                rr=aff(list(fam)+eq)
                if rr is not None:new.add(rr)
        families=new;counts.append(len(families));print('SINGLE',ci,len(families),'ranks',sorted({len(f)for f in families}),time.monotonic()-start,flush=True)
        if not families:break
        if len(families)>10000:raise TimeoutError('family budget')
    except TimeoutError as exc:complete=False;print('STOP',str(exc),flush=True)
    finally:signal.alarm(0)
    certified=[];unique=under=0;sets=sorted({S for cell in cells.values()for S in cell['sets']})
    if complete:
      for fam in families:
        if len(fam)<14:under+=1;continue
        unique+=1;h=[row[-1]for row in fam];assert all(row[j]==Q(i==j)for i,row in enumerate(fam)for j in range(14));h1,h2=h[:7],h[7:];eq=[]
        for S in sets:
            z=[max(sum(row[i]for i in S),Q(0))for row in A];target=Q(1-int(0 in S));value=target-sum(max(sum(w*x for w,x in zip(row,z)),Q(0))for row in plus)+sum(max(sum(w*x for w,x in zip(row,z)),Q(0))for row in(h1,h2));eq.append(z+[value])
        rr=aff(eq)
        if rr is None:continue
        assert len(rr)==7;R=[row[-1]for row in rr];head=R+[Q(1),Q(-1)];nn=json.loads(json.dumps(net));nn['second_layer']=[list(map(str,head)),list(map(str,[-x for x in head]))]+[list(map(str,row+[Q(0)]*2))for row in plus+[h1,h2]];nn['output']=['1','-1','1','1','1','-1','-1'];path=HERE/f'overnight_fixed_p4_threecarriers_candidate_{len(certified)}.json';path.write_text(json.dumps(nn,sort_keys=True,indent=2)+'\n')
        try:receipt=globalcheck(path)
        except AssertionError:continue
        certified.append({'path':path.name,'receipt':receipt})
    report={'status':'EXACT_THREE_CARRIER_CONTINUOUS_CURVATURE_GATE','complete':complete,'family_counts':counts,'families':[[[str(x)for x in row]for row in f]for f in families],'unique_pairs':unique,'underdetermined_pairs':under,'certified':certified,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Only σ(a-c)+σ(a-d)+σ(q-r) with two arbitrary negative outer units and arbitrary W7 remainder. Does not decide general five-free-term construction.'};(HERE/'overnight_fixed_p4_threecarriers.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print('DONE',complete,len(families),unique,under,certified,time.monotonic()-start,flush=True)
if __name__=='__main__':main()
