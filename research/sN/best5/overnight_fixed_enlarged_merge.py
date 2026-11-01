"""Merge two old activation patterns and adapt the enlarged first arrangement.

Unlike deleting a neuron, the merged seed introduces new zero hyperplanes.
The coefficients are then freed completely within its activation pattern.
This is a finite constructive search, not a negative result.
"""
import argparse,hashlib,itertools,json,math,signal,time
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_fullpair_dictionary import PERMS,primitive
from overnight_fixed_enlarged_first import refine,network
from overnight_fixed_enlarged_verify import check


def enlarged(first14,forms):
    H=set()
    for perm in PERMS:
        rank={i:k for k,i in enumerate(perm)};active=[]
        for a in first14:
            i=a.index(1);j=a.index(-1);active.append(a if rank[i]<rank[j]else[0]*5)
        for w in forms:
            g=[sum(c*a[i]for c,a in zip(w,active))for i in range(5)];v=[sum(g[perm[i]]for i in range(k))for k in range(1,5)]
            if min(v)<0<max(v):
                den=math.lcm(*(c.denominator for c in g));H.add(primitive([int(c*den)for c in g]))
    H.difference_update(primitive(a)for a in first14)
    return first14+[list(h)for h in sorted(H)]


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--budget',type=int,default=240);args=ap.parse_args();start=time.monotonic();prefix='overnight_fixed_enlarged_merge';known=json.loads(Path('overnight_fixed_fullpair_pattern_control_net.json').read_text());first14=known['first_layer'][:14];old=[list(map(Q,row[:14]))for row in known['second_layer'][2:]];out=list(map(int,known['output'][2:]));records=[];found=False;signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('declared budget')));signal.alarm(args.budget)
    try:
        for a,b in itertools.combinations(range(4),2):
            other=[i for i in range(4)if i not in(a,b)]
            for ratio in map(Q,('1','-1','2','1/2','-2','-1/2')):
                forms=[[x+ratio*y for x,y in zip(old[a],old[b])]]+[old[i]for i in other];first=enlarged(first14,forms);initial=[w+[Q(0)]*(len(first)-14)for w in forms]
                for sign in(1,-1):
                    outputs=[sign]+[out[i]for i in other];r=refine(first,initial,outputs);record={'merged':[a,b],'ratio':str(ratio),'merged_sign':sign,**{k:v for k,v in r.items()if k!='candidate'}};records.append(record);print(json.dumps({**record,'seconds':time.monotonic()-start}),flush=True)
                    if'candidate'in r:
                        cpath=Path(prefix+'_candidate.json');npath=Path(prefix+'_net.json');cpath.write_text(json.dumps(r['candidate'],indent=2)+'\n');npath.write_text(json.dumps(network(r['candidate']),indent=2)+'\n');receipt=check(npath,cpath);Path(prefix+'_check.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');found=True;break
                if found:break
            if found:break
    except TimeoutError:print('DECLARED_BUDGET_REACHED',flush=True)
    finally:signal.alarm(0)
    result={'status':'EXACT_LARGER_FIRST_LAYER_SECOND_WIDTH_FIVE'if found else'FINITE_MERGED_PATTERN_SEARCH_INCOMPLETE','records':records,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path(prefix+'.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='records'}),flush=True)

if __name__=='__main__':main()
