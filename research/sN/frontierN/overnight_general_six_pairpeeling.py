"""Uniform two-winner span obstruction, with explicit cut-removal witnesses.

For the same active rows at two strict points with maximum labels a,b, (Cell)
implies e_a-e_b lies in their span. A cut not separating a,b has zero root sum.
If exactly one active row crosses it and its coefficient sum is nonzero by
signs, that row's spanning coefficient is zero. Iteration cannot disconnect a,b.
No row coefficient magnitude is used. Independent checker pending.
"""
from itertools import combinations
from pathlib import Path
import json,time
from overnight_general_six_peeling import prep

BASE=Path(__file__).with_suffix('')

def check(fam,signs,flags):
    cells={}
    for lead,eps,a in flags:
        active=sum(1<<j for j,k in enumerate(lead) if signs[j][k]*eps[j]>0)
        cells.setdefault(active,set()).add(a)
    cuts={}
    for C in range(1,32):
        crossing=nonzero=0
        for j,(sup,sgn) in enumerate(zip(fam,signs)):
            inside=[sgn[k] for k,i in enumerate(sup) if C>>i&1]
            outside=[sgn[k] for k,i in enumerate(sup) if not(C>>i&1)]
            if not inside or not outside:continue
            crossing|=1<<j
            if len(set(inside))==1 or len(set(outside))==1:nonzero|=1<<j
        cuts[C]=(crossing,nonzero)
    for initial,winners in cells.items():
        for a,b in combinations(sorted(winners),2):
            active=initial;steps=[]
            while True:
                old=active
                for C,(crossing,nonzero) in cuts.items():
                    if bool(C>>a&1)!=bool(C>>b&1):continue
                    one=active&crossing
                    if one and one&(one-1)==0 and one&nonzero:
                        j=one.bit_length()-1;steps.append([C,j]);active^=one
                if active==old:break
            for C,(crossing,_) in cuts.items():
                if bool(C>>a&1)!=bool(C>>b&1) and not(active&crossing):
                    return {'active':initial,'winner_a':a,'winner_b':b,'steps':steps,'separating_cut':C}
    return None

def main():
    start=time.monotonic();source=json.loads(Path(__file__).with_name('overnight_general_six_full.json').read_text())
    out={'status':'Exact sign-based finite diagnostic; independent checker pending','completed':[]}
    for rec in source['completed']:
        if not rec['survivors']:continue
        fam=rec['family'];_,flags=prep(fam);excluded=[];survivors=[]
        for signs in rec['survivors']:
            cert=check(fam,signs,flags)
            if cert:excluded.append({'signs':signs,'certificate':cert})
            else:survivors.append(signs)
        r={'family_index':rec['family_index'],'family':fam,'tested':len(rec['survivors']),
           'excluded':excluded,'survivors':survivors};out['completed'].append(r)
        out['seconds']=time.monotonic()-start
        BASE.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
        print('family',rec['family_index'],'tested',r['tested'],'survivors',len(survivors),flush=True)

if __name__=='__main__':main()
