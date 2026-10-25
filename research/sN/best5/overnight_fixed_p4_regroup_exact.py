"""Continuous curvature-compatibility solve for all38 regroup candidates.

For every first-layer cell with a nonzero target curvature, the prospective
single preactivation gradient is fixed up to sign. Branches are exact affine
linear systems in seven real coefficients, not a coefficient dictionary.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations
import json,time,hashlib
from overnight_fixed_bowtie_verify import rref
from overnight_fixed_cross_verify import check as globalcheck
HERE=Path(__file__).resolve().parent


def affine(rows):
    rr=rref(rows)
    if any(not any(row[:-1])and row[-1]for row in rr):return None
    return rr


def main():
    start=time.monotonic();net=json.loads((HERE/'overnight_fixed_cross_net9_14_simple.json').read_text());A=[[Q(x)for x in r]for r in net['first_layer'][:7]];W=[[Q(x)for x in r[:7]]for r in net['second_layer'][2:]];D=list(map(Q,net['output'][2:]));cells={}
    for p in permutations(range(5)):
        rank={v:i for i,v in enumerate(p)};act=[]
        for row in A:
            i=next(i for i,x in enumerate(row)if x>0);j=next(i for i,x in enumerate(row)if x<0);act.append(row if rank[i]<rank[j]else[Q(0)]*5)
        key=tuple(any(r)for r in act);cell=cells.setdefault(key,{'active':act,'sets':set()});cell['sets'].update(tuple(sorted(p[:t]))for t in range(1,5))
    for cell in cells.values():
        act=cell['active'];curv={}
        for k,(d,w)in enumerate(zip(D,W)):
            g=tuple(sum(w[j]*act[j][i]for j in range(7))for i in range(5));vals=[sum(g[j]for j in S)for S in cell['sets']]
            if min(vals)<0<max(vals):
                scale=next(x for x in g if x);normal=tuple(x/scale for x in g);curv.setdefault(normal,[Q(0)]*12)[k]=d*abs(scale)
        cell['curvature']=curv
    results=[];certified=[]
    for ca in json.loads((HERE/'overnight_fixed_p4_regroup_cells.json').read_text())['candidates']:
        inds=ca['indices'];sgn=ca['curvature_sign'];conditions=[]
        for key,cell in cells.items():
            nonzero=[(normal,sum(cs[k]for k in inds))for normal,cs in cell['curvature'].items()if sum(cs[k]for k in inds)];assert len(nonzero)<=1
            if nonzero:
                normal,c=nonzero[0];assert c*sgn>0;act=cell['active'];coeff=[[act[j][i]for j in range(7)]for i in range(5)];rhs=[abs(c)*v for v in normal];conditions.append((len(rref(coeff)),key,coeff,rhs))
        conditions.sort(reverse=True);families={()};sizes=[]
        for rank,key,co,rhs in conditions:
            new=set()
            for fam in families:
                for s in(-1,1):
                    rr=affine(list(fam)+[row+[s*b]for row,b in zip(co,rhs)])
                    if rr is not None:new.add(rr)
            families=new;sizes.append(len(families))
            if not families:break
        out={'indices':inds,'curvature_sign':sgn,'branch_counts':sizes,'affine_family_count':len(families),'families':[[[str(x)for x in row]for row in fam]for fam in families]};unique=under=0
        for fam in families:
            if len(fam)<7:under+=1;continue
            unique+=1;h=[row[-1]for row in fam];assert all(row[j]==Q(i==j)for i,row in enumerate(fam)for j in range(7));eq=[]
            for S in sorted({S for cell in cells.values()for S in cell['sets']}):
                z=[max(sum(row[i]for i in S),Q(0))for row in A];value=sum(D[k]*max(sum(w*x for w,x in zip(W[k],z)),Q(0))for k in inds)-sgn*max(sum(w*x for w,x in zip(h,z)),Q(0));eq.append(z+[value])
            rr=affine(eq)
            if rr is None:continue
            assert len(rr)==7;rem=[row[-1]for row in rr];newnet=json.loads(json.dumps(net));head=[Q(v)for v in newnet['second_layer'][0]];head[:7]=[x+y for x,y in zip(head[:7],rem)];newnet['second_layer']=[list(map(str,head)),list(map(str,[-x for x in head]))]+[list(map(str,W[k]+[Q(0),Q(0)]))for k in range(12)if k not in inds]+[list(map(str,h+[Q(0),Q(0)]))];newnet['output']=['1','-1']+[str(D[k])for k in range(12)if k not in inds]+[str(sgn)];p=HERE/f'overnight_fixed_p4_regroup_candidate_{len(certified)}.json';p.write_text(json.dumps(newnet,sort_keys=True,indent=2)+'\n')
            try:receipt=globalcheck(p)
            except AssertionError as exc:out.setdefault('global_failures',[]).append(str(exc));continue
            certified.append({'file':p.name,'receipt':receipt});out.setdefault('certified',[]).append(p.name)
        out.update(unique_preactivations=unique,underdetermined_families=under);results.append(out)
    report={'status':'EXACT_CONTINUOUS_SUBSET_REGROUP_COMPATIBILITY_GATE','results':results,'certified':certified,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'All38 subsets passing the complete first-layer-cell curvature gate. An empty affine family is an exact impossibility for that fixed subset; underdetermined families remain open. No general five-free-term theorem.'};(HERE/'overnight_fixed_p4_regroup_exact.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({'seconds':report['seconds'],'candidates':len(results),'inconsistent':sum(not x['affine_family_count']for x in results),'underdetermined':sum(x['underdetermined_families']for x in results),'unique':sum(x['unique_preactivations']for x in results),'certified':certified},sort_keys=True),flush=True)
if __name__=='__main__':main()
