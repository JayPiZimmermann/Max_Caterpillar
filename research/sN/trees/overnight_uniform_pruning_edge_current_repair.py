"""Bounded gates for summing/averaging the current over exact head slides.

Canonical N5 exact rows, canonical N7 saved modular rows, and all N5
augmented-tree head-exchange identities. No larger-family sweep.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,time
import numpy as np
import networkx as nx
import sympy as S
from overnight_uniform_pruning_edge_current import signed_roots,fmpq,fmpq_mat,HERE
from overnight_uniform_pruning_signed7 import reduce

def reachable(E,start,reverse):
    A={start};todo=[start]
    for x in todo:
        for u,v in E:
            if reverse:u,v=v,u
            if u==x and v not in A:A.add(v);todo.append(v)
    return sorted(A)

def repaired(E,head,n):
    r,s=head;E=list(map(tuple,E));P=reachable(E,r,True);M=reachable(E,s,False);k=[0]*n
    for u,v in E:k[u]+=1
    k[r]+=1;k[s]-=1
    total=0
    for u,v in itertools.product(P,M):
        G=nx.Graph(E+[(u,v)]);J=signed_roots(G);out=k[:];out[v]+=1
        a=[out[x]*J[x]for x in range(n)];K=[n*x-sum(a)for x in a]
        G.remove_edge(u,v);C=nx.node_connected_component(G,u)
        total+=sum(J[x]for x in C)*(K[u]-K[v])-sum(K[x]for x in C)*(J[u]-J[v])
    return total,len(P)*len(M)

def exact_gate(rows,values):
    M=fmpq_mat([[fmpq(x)for x in row[:-1]]for row in rows]);R,rank=M.rref();n=len(values);piv=[next(j for j in range(n)if R[i,j])for i in range(rank)];bad=[]
    for j in range(n):
        if j in piv:continue
        v=[Q(0)]*n;v[j]=1
        for i,k in enumerate(piv):v[k]=-Q(str(R[i,j]))
        pairing=sum(x*y for x,y in zip(v,values))
        if pairing:bad.append((sum(bool(x)for x in v),v,pairing))
    ans={'score_compatible':not bad,'rank':rank}
    if bad:
        _,v,pairing=min(bad,key=lambda t:t[0]);ans.update(relation={str(i):str(x)for i,x in enumerate(v)if x},pairing=str(pairing))
    else:
        A=S.Matrix(rows).applyfunc(S.Rational);w,pars=A[:,:-1].T.gauss_jordan_solve(S.Matrix(values));w=w.subs({p:0 for p in pars});ans['target_response']=str((w.T*A[:,-1])[0])
    return ans

def main():
    start=time.monotonic();data=json.loads((HERE/'overnight_uniform_pruning_signed_gate.json').read_text());values=[repaired(u['edges'],(u['root'],0),5)for u in data['units']];out={'status':'ROOT_SLIDE_REPAIRED_CURRENT_GATE','N5':{}}
    for mode in('sum','average'):
        q=[Q(t,c if mode=='average'else 1)for t,c in values];out['N5'][mode]=exact_gate(data['rows'],q);out['N5'][mode]['values']=list(map(str,q));print('N5',mode,{k:v for k,v in out['N5'][mode].items()if k!='values'},flush=True)
    headtests=0;failures={}
    for G in nx.nonisomorphic_trees(5):
        E=list(G.edges)
        for bits in itertools.product((0,1),repeat=4):
            oriented=[(v,u)if b else(u,v)for(u,v),b in zip(E,bits)];qs=[repaired(oriented[:i]+oriented[i+1:],oriented[i],5)for i in range(4)];headtests+=1
            for mode in('sum','average'):
                val=sum(Q(t,c if mode=='average'else 1)for t,c in qs)
                if val and mode not in failures:failures[mode]={'oriented_tree':oriented,'head_scores':[[str(t),c]for t,c in qs],'head_sum':str(val)}
    out['head_exchange']={'oriented_augmented_trees_tested':headtests,'first_failures':failures};print('head exchange',out['head_exchange'],flush=True)
    saved=json.loads((HERE/'overnight_uniform_pruning_signed7.json').read_text());p=saved['prime'];units=saved['units'];A=np.fromfile(HERE/'overnight_uniform_pruning_signed7.u32',dtype='<u4').reshape(saved['rows'],len(units)+1).astype(np.int64);basis={}
    for row in A:
        v=reduce(row,basis,p);nz=np.flatnonzero(v[:-1])
        if len(nz):j=int(nz[0]);basis[j]=v*pow(int(v[j]),-1,p)%p
        else:assert v[-1]==0
    vv=[repaired(u['edges'],(u['root'],0),7)for u in units];out['N7']={}
    for mode in('sum','average'):
        q=[t*pow(c,-1,p)%p if mode=='average'else t%p for t,c in vv];rem=reduce(q+[0],basis,p);out['N7'][mode]={'status':'MODULAR_ONLY','score_compatible':bool(np.all(rem[:-1]==0)),'target_response_if_compatible':int(-rem[-1]%p)};print('N7',mode,out['N7'][mode],flush=True)
    out['seconds']=time.monotonic()-start;out['scope']='Any nonzero head-exchange sum is an exact analytic refutation, independently of Fourier rows. Canonical matrix gates retain their exact-grid/modular status.';Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('seconds',out['seconds'],flush=True)
if __name__=='__main__':main()
