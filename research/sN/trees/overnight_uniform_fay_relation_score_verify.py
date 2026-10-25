"""Independent direct signed-order check of the four-feature score failure."""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,time
HERE=Path(__file__).parent

def main():
    start=time.monotonic();z=list(map(int,(HERE/'overnight_uniform_fay_relation12.txt').read_text().split()));rows=[];total=Q(0)
    for j in range(z[0]):
        w,root,*flat=z[1+16*j:1+16*(j+1)];E=set(zip(flat[::2],flat[1::2]));T={v:set()for v in range(1,9)}
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
        A=sum(len(T[v])*I[v]for v in T);B=sum(chi[v]*len(T[v])*I[v]for v in T);D1=G1=0
        for v in T:
            dist={v:0};todo=[v]
            for u in todo:
                for a in T[u]:
                    if a not in dist:dist[a]=dist[u]+1;todo.append(a)
            for u in T:
                q=dist[u]*I[v]*I[u];D1+=q;G1+=(len(T[v])+len(T[u]))*q
        score=epsilon*(Q(2,3)*A*A+2*B*B-Q(10,3)*D1+G1);total+=w*score;rows.append({'coefficient':w,'root':root,'edges':sorted(E),'signed_root_counts':I,'epsilon':epsilon,'A':A,'B':B,'D1':D1,'G1':G1,'score':str(score)})
    assert total==Q(-2048,3)
    out={'status':'INDEPENDENT_EXACT_FOUR_FEATURE_SCORE_REFUTATION','score_pairing':str(total),'units':rows,'scope':'Combined with the independent whole-function identity checker, this disproves the four-feature score as a linear functional. No claim about all possible perfect-matching separators.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':main()
