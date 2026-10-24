"""Emit cut-peeling traces for the two profiles not excluded by pair peeling."""
from pathlib import Path
import json
from overnight_general_six_peeling import prep,solve

def main():
    source=json.loads(Path(__file__).with_name('overnight_general_six_pairpeeling.json').read_text())
    rec=next(r for r in source['completed'] if r['family_index']==33)
    fam=rec['family'];comps,flags=prep(fam);certs=[]
    for signs in rec['survivors']:
        cells=set()
        for lead,eps,a in flags:
            active=sum(1<<j for j,k in enumerate(lead) if signs[j][k]*eps[j]>0)
            cells.add((active,a))
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
        bits=0
        for active,a in cells:bits|=comps[active][a]
        rounds=[]
        while True:
            fixed=solve(bits)
            if fixed is None:break
            changes=[];newcells=set()
            for initial,a in sorted(cells):
                active=initial;steps=[]
                while True:
                    old=active
                    for C,value in fixed.items():
                        if value!=int(bool(C>>a&1)):continue
                        crossing,nonzero=cuts[C];one=active&crossing
                        if one and one&(one-1)==0 and one&nonzero:
                            steps.append([C,one.bit_length()-1]);active^=one
                    if old==active:break
                if steps:changes.append({'active':initial,'winner':a,'steps':steps})
                newcells.add((active,a));bits|=comps[active][a]
            assert changes
            rounds.append(changes);cells=newcells
        certs.append({'signs':signs,'rounds':rounds})
    out={'family_index':33,'family':fam,'certificates':certs}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print('two exact traces emitted; rounds',[len(c['rounds']) for c in certs],flush=True)

if __name__=='__main__':main()
