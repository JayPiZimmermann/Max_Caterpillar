#!/usr/bin/env python3
"""Replay local-rule exclusions using inverse coordinate matrices."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,time
from flint import nmod_mat
from overnight_upper_baxter_bridge_check import matrix_term
from rational_identity import term,Verifier
HERE=Path(__file__).parent

def target(a):
    key,c=matrix_term(4,(-1,1,0,0),((1,2),(2,3)))
    num,power,den=key
    def lift(f):return f[:-1]+(f[a-1] if a else 0,)+(f[-1],)
    out=defaultdict(Q)
    for v in (a,4):
        f=(-1,-1,-1,-1,0) if v==0 else tuple(int(i==v-1) for i in range(4))+(0,)
        k,d=term(-c,lift(num),power,[(lift(g),m) for g,m in den]+[(f,1)])
        out[k]+=d
    return dict(out)

def evaluate(key,c,point,p):
    num,power,den=key;dot=lambda f:sum(x*y for x,y in zip(f[:-1],point))+f[-1]
    result=c.numerator*pow(c.denominator,-1,p)%p*pow(dot(num)%p,power,p)%p
    for f,m in den:result=result*pow(pow(dot(f)%p,m,p),-1,p)%p
    return result

def main():
    start=time.monotonic();results=[]
    paths=[HERE/'overnight_upper_baxter_vertex_split.json',HERE/'overnight_upper_baxter_vertex_completion.json']
    for path in paths:
        data=json.loads(path.read_text());records=data.get('records',[data]);p=data['prime']
        for record in records:
            a=record.get('split_label',3);rhs=target(a)
            if record['status']=='EXACT_LOCAL_VERTEX_SPLIT_IDENTITY':
                expr=defaultdict(Q,{k:-c for k,c in rhs.items()})
                for row in record['selected']:
                    key,c=matrix_term(5,row['head'],row['edges']);expr[key]+=Q(row['coefficient'])*c
                assert Verifier(150).check(dict(expr));results.append(dict(label=a,status='IDENTITY_REPLAYED'));continue
            sources=[matrix_term(5,row['head'],row['edges']) for row in record['sources']]
            rows=[]
            for point in record['points']:
                rows.append([evaluate(k,c,point,p) for k,c in sources]+[sum(evaluate(k,c,point,p) for k,c in rhs.items())%p])
            augmented=nmod_mat(rows,p).rank();ordinary=nmod_mat([row[:-1] for row in rows],p).rank()
            assert [ordinary,augmented]==record['ranks'] and augmented==ordinary+1
            kernels=record['kernels'];assert len(kernels)==len(sources)-ordinary
            # Each stored vector has its own free coordinate. Independence
            # is also checked directly, without relying on source ordering.
            matrix=[]
            for kernel in kernels:
                vector=[0]*len(sources);expr=defaultdict(Q)
                for j,raw in kernel:
                    c=Q(raw);k,d=sources[j];expr[k]+=c*d
                    vector[j]=c.numerator*pow(c.denominator,-1,p)%p
                assert Verifier(150).check(dict(expr));matrix.append(vector)
            assert nmod_mat(matrix,p).rank()==len(kernels)
            results.append(dict(label=a,status='EXACT_GAP_REPLAYED',ranks=[ordinary,augmented],kernels=len(kernels)))
    receipt=dict(status='INDEPENDENT_INVERSE_MATRIX_SPLIT_GATES_PASSED',results=results,
        inputs=[dict(path=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
        scope='Recomputes every sampled entry with inverse coordinates, proves every rational null relation, and checks null-vector independence. The general max-substitution Fourier law is the mathematical bridge.')
    (HERE/'overnight_upper_baxter_split_check.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt['status'],'SECONDS',receipt['seconds'],flush=True)

if __name__=='__main__':main()
