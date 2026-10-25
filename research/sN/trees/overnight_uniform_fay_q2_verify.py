"""Exact arithmetic and local moment controls for the live Q2 formula.

Standard library only. No descent or uniform separator assertion.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,math,time
HERE=Path(__file__).parent
COEFF={'all;d^0;parity^1;orientation^1;deg_prod':Q(2),
       'all;d^1;parity^0;orientation^1;one':Q(3,2),
       'all;d^1;parity^0;orientation^1;deg_sum':Q(-5,4),
       'all;d^2;parity^0;orientation^1;deg_prod':Q(1)}

def cross_mean(d,left,right):
    total=Q(0)
    for z in itertools.product((-1,1),repeat=d+1):
        u=z[0];v=z[-1];b=(1-u)//2;c=(1-v)//2
        first_a=2+left-b;first_c=1+b;delta1=first_c-first_a
        last_a=2+right*(1-c);last_c=1+right*c;delta2=last_c-last_a
        length=Q(3*d-sum(z[:d]),2)
        polynomial=delta1*delta2*length**2+2*length*(first_c*delta2*u+delta1*last_c)+first_c*delta2+delta1*last_c+2*first_c*last_c*u
        total+=math.prod(z[:d])*polynomial
    return total/(2**(d+1))

def target_formula(q):
    if q==2:return Q(0)
    choose=lambda d:math.comb(2*q-2,q-1-d) if q-1-d>=0 else 0
    return Q(2**q)*(5-4*(-1)**q-(q-1)*(q-2)-2*choose(1)+choose(2)+choose(3))

def main():
    start=time.monotonic();D=json.loads((HERE/'overnight_uniform_fay.json').read_text());keys=D['features'];weights=[COEFF.get(k,Q(0))for k in keys]
    dot=lambda row:sum(a*int(b)for a,b in zip(weights,row))
    assert all(dot(r)==0 for r in D['independent_constraint_rows'])
    sequence=json.loads((HERE/'overnight_uniform_fay_sequence_gate.json').read_text());assert dot(sequence['twelve_term_constraint_exact'])==0
    targets=[]
    for q,row in sequence['exact_signed_caterpillar_vectors'].items():
        q=int(q);value=dot(row);assert value==target_formula(q);targets.append({'q':q,'signed_sum':str(value),'maximum_response_if_descent':str(value/math.factorial(2*q+1))})
    table=[]
    expected={1:[Q(-3),Q(-7,2),Q(-7,2),Q(-7,2)],2:[Q(-1,2),Q(0),Q(0),Q(1,2)],3:[Q(1,2)]*4,4:[Q(0)]*4,5:[Q(0)]*4}
    for d in range(1,6):
        values=[cross_mean(d,l,r)for l,r in itertools.product((0,1),repeat=2)];assert values==expected[d];table.append({'distance':d,'boundary_order':'(0,0),(0,1),(1,0),(1,1)','means':list(map(str,values))})
    # Independently recompute the live score on the12 whole-function terms.
    words=list(map(int,(HERE/'overnight_uniform_fay_relation12.txt').read_text().split()));pairing=Q(0);scores=[]
    for j in range(words[0]):
        w,root,*flat=words[1+16*j:1+16*(j+1)];E=set(zip(flat[::2],flat[1::2]));T={v:set()for v in range(1,9)}
        for a,b in E:T[a].add(b);T[b].add(a)
        I={v:0 for v in T}
        for p in itertools.permutations(range(1,9)):
            seen={p[0]}
            for v in p[1:]:
                if not(T[v]&seen):break
                seen.add(v)
            else:I[p[0]]+=(-1)**sum(p[a]>p[b]for a in range(8)for b in range(a+1,8))
        parent={root:None};chi={root:1};todo=[root];epsilon=1
        for v in todo:
            for u in T[v]:
                if u!=parent[v]:parent[u]=v;chi[u]=-chi[v];todo.append(u);epsilon*=1 if(u,v)in E else-1
        B=sum(chi[v]*len(T[v])*I[v]for v in T);D1=G1=H2=0
        for v in T:
            dist={v:0};todo=[v]
            for u in todo:
                for a in T[u]:
                    if a not in dist:dist[a]=dist[u]+1;todo.append(a)
            for u in T:
                term=dist[u]*I[v]*I[u];D1+=term;G1+=(len(T[v])+len(T[u]))*term;H2+=dist[u]*len(T[v])*len(T[u])*term
        value=epsilon*(2*B*B+Q(3,2)*D1-Q(5,4)*G1+H2);scores.append(str(value));pairing+=w*value
    assert pairing==0
    out={'status':'EXACT_Q2_LOCAL_MOMENT_AND_GLOBAL_IDENTITY_CONTROLS_PASS','coefficients':{k:str(v)for k,v in COEFF.items()},'known_local_constraints_pass':True,'twelve_term_pairing_independently_recomputed':str(pairing),'twelve_term_scores':scores,'moment_table':table,'target_checks':targets,'scope':'These checks support the uniform local-Fay and target-moment calculations in the note. They do not construct a linear functional or establish descent through all global identities.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':main()
