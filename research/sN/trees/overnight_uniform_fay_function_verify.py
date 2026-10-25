"""Independent exact whole-function identity check in ordered-coordinate gaps.

Standard library only. Directly counts the first-layer intervals and then
consolidates the second-layer walls on the positive gap orthant. No Fourier
producer, score routine, matrix computation, or C++ code is imported.
"""
from pathlib import Path
from collections import defaultdict
import itertools,json,math,time

HERE=Path(__file__).parent

def main():
    before=time.monotonic();ints=list(map(int,(HERE/'overnight_uniform_fay_relation12.txt').read_text().split()));m=ints[0];assert len(ints)==1+16*m;units=[]
    for j in range(m):
        w,r,*flat=ints[1+16*j:1+16*(j+1)];E=list(zip(flat[::2],flat[1::2]));assert w in(-1,1) and 1<=r<=8
        reached={1}
        while True:
            new=reached|{a for a,b in E if b in reached}|{b for a,b in E if a in reached}
            if new==reached:break
            reached=new
        assert reached==set(range(1,9))and len({frozenset(e)for e in E})==7
        units.append((w,r,E))
    counts=defaultdict(int);linear=[0]*8;permutations=0
    intervals={(a,b):tuple(range(a,b))for a in range(9)for b in range(a,9)}
    for p in itertools.permutations(range(9)):
        for w,r,E in units:
            beta=[0]*8;a=p[0];b=p[r];sign=1 if b>a else-1
            for k in intervals[min(a,b),max(a,b)]:beta[k]+=sign
            for u,v in E:
                a=p[v];b=p[u]
                if b>a:
                    for k in intervals[a,b]:beta[k]+=1
            lo=min(beta);hi=max(beta)
            if lo>=0:
                for k in range(8):linear[k]+=w*beta[k]
            elif hi>0:
                g=math.gcd(*beta);sgn=1 if next(x for x in beta if x)>0 else-1
                key=tuple(x//(g*sgn)for x in beta);counts[key]+=w*g
                if sgn<0:
                    for k in range(8):linear[k]+=w*beta[k]
        permutations+=1
        if permutations%50000==0:print('permutations',permutations,'seconds',time.monotonic()-before,flush=True)
    assert permutations==math.factorial(9)
    assert not any(counts.values()),'Nonzero wall in the interior of the ordered chamber'
    assert linear==[0]*8,'Nonzero remaining linear function'
    out={'status':'INDEPENDENT_EXACT_N9_WHOLE_FUNCTION_IDENTITY','arity':9,'units':m,'all_label_permutations':permutations,'distinct_mixed_gap_walls':len(counts),'nonzero_wall_coefficients':0,'linear_gap_coefficients':linear,'scope':'The unaveraged full symmetric signed sum vanishes on the open ordered chamber by exact ReLU wall consolidation. Permutation symmetry and continuity extend it to all real inputs. Therefore the corresponding rational-kernel relation also holds. No frequency samples or rank assumptions.','seconds':time.monotonic()-before};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':main()
