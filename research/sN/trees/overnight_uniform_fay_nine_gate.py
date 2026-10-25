"""Whole surviving feature space against the cached N9 PM+star rows.

Only extracts small proposed relations. Exact whole-function checks are
performed separately; no sampled relation is promoted to an identity here.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,math,time
import numpy as np
from overnight_uniform_fay import HERE,KEYS,vec,P,add,reduce
from overnight_uniform_fay_global_gate import nullspace
from flint import nmod_mat,ctx

def reconstruct(a):
    a%=P
    if a>P//2:a-=P
    if abs(a)<=1000:return Q(a)
    r0,r1=P,a%P;t0,t1=0,1;bound=math.isqrt(P//2)
    while abs(r1)>bound:
        q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
    if t1 and abs(t1)<=bound and math.gcd(r1,t1)==1:
        r=Q(r1,t1)
        if (r.numerator-a*r.denominator)%P==0:return r
    return None

def main():
    ctx.threads=1;start=time.monotonic();D=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());classes=json.loads((HERE/'overnight_uniform_q9_quotient.json').read_text())['class_data'];state=json.loads((HERE/'overnight_uniform_q9_rows_state.json').read_text());K=np.array(json.loads((HERE/'overnight_uniform_fay_analyze.json').read_text())['integer_nullspace_columns'],dtype=np.int64).T%P;G=json.loads((HERE/'overnight_uniform_fay_global_gate.json').read_text());basis={}
    for r in G['global_constraints_on_local_nullspace']:add(r,basis)
    cols=[]
    for c in classes:
        deg={v:0 for v in range(1,9)}
        for a,b in c['underlying_edges']:deg[a]+=1;deg[b]+=1
        if c['matching']==4 or max(deg.values())==7:cols.append(c['representative'])
    M=np.fromfile(HERE/state['matrix'],dtype='<u4').reshape(state['rows'],len(D['units'])+1);R,rank=nmod_mat(M[:,cols].tolist(),P).rref();piv=[];at=0
    for i in range(rank):
        while not R[i,at]:at+=1
        piv.append(at);at+=1
    F=np.array([vec(D['units'][j])%P for j in cols],dtype=np.int64)@K%P;relations=[]
    for j in range(len(cols)):
        if j in piv:continue
        rel={cols[j]:1};coeff=np.array([int(R[i,j])for i in range(rank)],dtype=np.int64);row=(F[j]-coeff@F[piv])%P
        if not np.any(row):continue
        for i,k in enumerate(piv):
            if coeff[i]:rel[cols[k]]=-int(coeff[i])%P
        relations.append((len(rel),j,row,rel))
    selected=[]
    for size,j,row,rel in sorted(relations,key=lambda x:x[:2]):
        if not add(row,basis):continue
        rational={i:reconstruct(c)for i,c in rel.items()};entry={'support':size,'raw_relation_mod':rel,'constraint_mod':list(map(int,row))}
        if all(c is not None for c in rational.values()):
            scale=math.lcm(*(c.denominator for c in rational.values()));integer={i:int(c*scale)for i,c in rational.items()};entry['integer_relation_proposal']=integer
            lines=[]
            for i,c in integer.items():
                U=D['units'][i];lines.append(' '.join(map(str,[c,U['root']]+[v for e in U['edges']for v in e])))
            path=HERE/f'overnight_uniform_fay_global_rel_{len(selected)}.txt';path.write_text(str(len(lines))+'\n'+'\n'.join(lines)+'\n');entry['declaration_file']=path.name
        selected.append(entry)
    C=[list(map(int,r))for r in basis.values()];V,cr=nullspace(np.array(C,dtype=np.int64));T=json.loads((HERE/'overnight_uniform_fay_sequence_gate.json').read_text())['exact_signed_caterpillar_vectors'];detectable={q:bool(np.any(((np.array([x%P for x in t],dtype=np.int64)@K)%P)@V%P))for q,t in T.items()};out={'status':'MODULAR_N9_GLOBAL_FEATURE_RELATION_PROPOSALS','rows':state['rows'],'columns':len(cols),'evaluation_rank':rank,'additional_selected_relations':selected,'total_constraint_rank_mod':cr,'targets_q2_to_q10_detectable_mod':detectable,'scope':'Each selected integer relation remains a proposal until an independent whole-function or rational-function identity check passes. No new evaluation rows or features.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='additional_selected_relations'},indent=2),flush=True);print('selected supports',[r['support']for r in selected],flush=True)

if __name__=='__main__':main()
