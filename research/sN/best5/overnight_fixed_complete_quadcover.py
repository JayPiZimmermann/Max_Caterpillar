"""Closed complete cover by chosen zero cores on the five quadruple rays.

The 12 cases are orbits under S5 and same-output-sign neuron exchange.
They do not impose nonzero conditions on the unchosen coordinates.
"""
from pathlib import Path
from itertools import combinations
from fractions import Fraction as Q
import hashlib,json,resource,sys,time
sys.path.insert(0,'/tmp/overnight_fixed_z3')
import z3
from overnight_fixed_anchor_verify import check

HERE=Path(__file__).resolve().parent

def main():
    mode=sys.argv[1]if len(sys.argv)>1 else'p2'
    seconds=int(sys.argv[2])if len(sys.argv)>2 else 15
    resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
    z3.set_param('parallel.enable',False)
    source=HERE/('overnight_fixed_complete_decide_'+mode+'.smt2')
    assertions=list(z3.parse_smt2_file(str(source)))
    # Last assertion orders the two same-sign cores by an arbitrary score.
    # Remove it: the cover uses their zero-ray counts as representative choice.
    assert len(assertions)==191 and z3.is_le(assertions[-1])
    base=assertions[:-1]
    pairs=list(combinations(range(5),2))
    W=[[z3.Real(f'w{k}_{j}')for j in range(14)]for k in range(3)]
    signs=[1,1,-1]if mode=='p2'else[1,-1,-1]
    majority=(0,1)if mode=='p2'else(1,2)
    triples=[(a,b,5-a-b)for a in range(6)for b in range(6-a)]
    triples=[n for n in triples if n[majority[0]]<=n[majority[1]]]
    assert len(triples)==12
    records=[];start=time.monotonic()
    for idx,n in enumerate(triples):
        solver=z3.SolverFor('QF_LRA');solver.set(timeout=1000*seconds,max_memory=2500)
        solver.add(*base);omitted=0
        for k,count in enumerate(n):
            for o in range(omitted,omitted+count):
                S=set(range(5))-{o}
                row=[int(i in S and j not in S)for i,j in pairs]+[int(i in S)-int(4 in S)for i in range(4)]
                solver.add(z3.Sum([a*v for a,v in zip(row,W[k])if a])==0)
            omitted+=count
        before=time.monotonic();answer=solver.check()
        r={'index':idx,'counts':n,'status':str(answer),'seconds':time.monotonic()-before}
        if answer==z3.unknown:r['reason']=solver.reason_unknown()
        if answer==z3.sat:
            model=solver.model()
            def value(v):
                q=model.eval(v,model_completion=True)
                return Q(q.numerator_as_long(),q.denominator_as_long())
            wc=[[value(v)for v in w]for w in W]
            def residual(S):
                row=[int(i in S and j not in S)for i,j in pairs]+[int(i in S)-int(4 in S)for i in range(4)]
                return 1-int(4 in S)-sum(d*max(Q(0),sum(a*v for a,v in zip(row,w)))for d,w in zip(signs,wc))
            c=[residual({i})for i in range(5)]
            q=[residual({i,j})-c[i]-c[j]for i,j in pairs]
            rc=[-v for v in q]+[c[i]+sum(q[e]for e,(a,b)in enumerate(pairs)if a==i)for i in range(4)]
            A=[[Q(k==i)-Q(k==j)for k in range(5)]for i,j in pairs]+[[Q(k==4)-Q(k==i)for k in range(5)]for i in range(4)]+[[Q(k==4)*s for k in range(5)]for s in(1,-1)]
            def compile(w,head=False):
                v=w[:10]+[Q(0)]*6
                for i in range(4):v[pairs.index((i,4))]+=w[10+i];v[10+i]-=w[10+i]
                if head:v[-2:]=[Q(1),Q(-1)]
                return v
            h=compile(rc,True)
            net={'N':5,'first_layer':[list(map(str,r))for r in A],'second_layer':[list(map(str,h)),list(map(str,[-v for v in h]))]+[list(map(str,compile(w)))for w in wc],'output':['1','-1']+list(map(str,signs))}
            path=HERE/f'overnight_fixed_complete_quadcover_{mode}_{idx}_network.json'
            path.write_text(json.dumps(net,indent=2)+'\n');r['network']=path.name;r['global_check']=check(path)
        print(json.dumps(r),flush=True);records.append(r)
        report={'scope':'Complete closed12casecover of the full real-coefficient K3 formula by quadruple-ray zero assignments. UNSAT needs independent proof; timeouts implynothing. Only independently globally checkedSAT is a construction.','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'mode':mode,'seconds_per_case':seconds,'elapsed':time.monotonic()-start,'cases':records}
        (HERE/f'overnight_fixed_complete_quadcover_{mode}.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
        if answer==z3.sat:break

if __name__=='__main__':main()
