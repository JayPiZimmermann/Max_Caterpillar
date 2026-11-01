"""Whole-domain exact template prepass for P4 four-free-term candidates.

Templates are rational equation combinations from the already checked K3
proofs, plus individual equations. Every rejection is a direct exact cone
contradiction. Surviving cases remain open, not declared feasible.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import product
import hashlib,json,signal,time
import overnight_root9_equations as E


def main():
    started=time.monotonic();E.initialize();here=Path(__file__).parent;inventory=json.loads((here/'overnight_root9_inventory.json').read_text());zs=sorted(map(int,inventory['flats']));covers=[inventory['flats'][str(z)]['cover']for z in zs];equation,_,_=E.case_data((zs[0],),(1,));rhs=[equation(i)[1]for i in range(49)];ts=set()
    for i,b in enumerate(rhs):
        if b:ts.add(((i,1/b),))
    for line in(here/'overnight_root9_cones.jsonl').read_text().splitlines():
        proof=json.loads(line)['proof'];assert proof[0]=='cone'and not proof[3];coeff={i:Q(c)for i,c in proof[1]};b=sum(c*rhs[i]for i,c in coeff.items());assert b>0;ts.add(tuple((i,c/b)for i,c in sorted(coeff.items())if c))
    templates=sorted(ts,key=lambda t:(len(t),t));assert all(sum(c*rhs[i]for i,c in t)==1 for t in templates);allowed=[]
    for z in zs:
        eq,forms,_=E.case_data((z,),(1,));rows=[eq(i)[0]for i in range(49)];positive=negative=0
        for j,t in enumerate(templates):
            combo={}
            for i,c in t:
                for k,v in rows[i].items():combo[k]=combo.get(k,Q(0))+c*v
            if all(c<=0 for c in combo.values()):positive|=1<<j
            if all(c>=0 for c in combo.values()):negative|=1<<j
        allowed.append((positive,negative))
    table={'templates':[[[i,str(c)]for i,c in t]for t in templates],'flats':zs,'allowed_template_bits':[[str(a),str(b)]for a,b in allowed],'scope':'Every template has right-hand side1; bits indicate all local absolute-value coefficients are nonpositive for the chosen output sign.'};tp=here/'overnight_fixed_p4_k4_templates_data.json';tp.write_text(json.dumps(table,sort_keys=True,indent=2)+'\n');print('PRECOMPUTED',len(templates),'templates',len(zs),'flats',time.monotonic()-started,flush=True)
    full=(1<<25)-1;eligible={};signs=list(product((0,1),repeat=4));counts=[0]*len(templates);quad_count=cases=rejected=survivors=surviving_quads=0;outpath=here/'overnight_fixed_p4_k4_template_survivors.jsonl';signal.signal(signal.SIGALRM,lambda *_:(_ for _ in()).throw(TimeoutError('120 second domain prepass')));signal.alarm(120);complete=True
    try:
        with outpath.open('w')as out:
            for i in range(len(zs)):
                ci=covers[i]
                for j in range(i,len(zs)):
                    cij=ci|covers[j]
                    for k in range(j,len(zs)):
                        missing=full&~(cij|covers[k])
                        if missing not in eligible:eligible[missing]=sum(1<<t for t,c in enumerate(covers)if c&missing==missing)
                        bits=eligible[missing]>>k
                        while bits:
                            bit=bits&-bits;bits-=bit;l=k+bit.bit_length()-1;quad_count+=1;openmask=0
                            for si,(s0,s1,s2,s3)in enumerate(signs):
                                common=allowed[i][s0]&allowed[j][s1]&allowed[k][s2]&allowed[l][s3];cases+=1
                                if common:counts[(common&-common).bit_length()-1]+=1;rejected+=1
                                else:survivors+=1;openmask|=1<<si
                            if openmask:
                                surviving_quads+=1;out.write(json.dumps({'flats':[zs[i],zs[j],zs[k],zs[l]],'sign_mask':openmask},separators=(',',':'))+'\n')
                if i%25==0:out.flush();print('DOMAIN',i,quad_count,cases,rejected,survivors,time.monotonic()-started,flush=True)
    except TimeoutError:complete=False;print('BUDGET_STOP',flush=True)
    finally:signal.alarm(0)
    if complete:assert quad_count==296861 and cases==4749776
    report={'status':'COMPLETE_EXACT_K4_TEMPLATE_PREPASS'if complete else'INCOMPLETE_EXACT_K4_TEMPLATE_PREPASS','flat_count':len(zs),'template_count':len(templates),'covering_quadruples':quad_count,'sign_cases':cases,'exact_template_exclusions':rejected,'remaining_cases':survivors,'remaining_quadruples':surviving_quads,'template_counts':counts,'seconds':time.monotonic()-started,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'template_data_sha256':hashlib.sha256(tp.read_bytes()).hexdigest(),'survivors_sha256':hashlib.sha256(outpath.read_bytes()).hexdigest(),'scope':'Whole finite real-parameter necessary domain screened by exact equation combinations; no lower bound until all survivors close and an independent complete-domain checker passes.'};(here/'overnight_fixed_p4_k4_templates.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='template_counts'},sort_keys=True),flush=True)
if __name__=='__main__':main()
