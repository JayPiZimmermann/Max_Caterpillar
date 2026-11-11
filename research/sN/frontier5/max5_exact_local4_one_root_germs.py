"""Necessary local-germ model for Max4: one root, two nonroot triple planes.
All positive-two-core orientation and assignment choices are enumerated.
Diagnostic until independent audit/proof replay.
"""
from pathlib import Path
import sys,itertools,json,time
sys.path.insert(0,'/tmp/max5_first11_z3')
import z3
HERE=Path(__file__).resolve().parent

def e(i):return [int(i==j) for j in range(4)]
def sub(a,b):return [x-y for x,y in zip(a,b)]
def main():
 u,v=z3.Reals('u v');r=[1,-1,0,0];out=[];t=time.monotonic();all_cases=[]
 for ma,mb,swap,sa, sb in itertools.product((0,2,3),(1,2,3),(0,1),itertools.product((1,-1),repeat=2),itertools.product((1,-1),repeat=2)):
  aa=[i for i in (0,2,3) if i!=ma];bb=[i for i in (1,2,3) if i!=mb]
  if swap:bb=bb[::-1]
  A=[0]*4;B=[0]*4;A[ma]=-1;A[aa[0]]=u;A[aa[1]]=1-u;B[mb]=-1;B[bb[0]]=v;B[bb[1]]=1-v
  s=z3.SolverFor('QF_LRA');s.add(u>0,u<1,v>0,v<1)
  global_rows=[]
  for k in range(3):
   L=[z3.Real(f'L{k}_{j}') for j in range(4)];c=z3.Real(f'c{k}')
   if k<2:
    ca=-sa[k];cb=-sb[k];ta=[sa[k]*x for x in sub(e(aa[k]),e(ma))];tb=[sb[k]*x for x in sub(e(bb[k]),e(mb))]
   else:
    ca=1-sum(x==-1 for x in sa);cb=1-sum(x==-1 for x in sb)
    ta=e(ma);tb=e(mb)
    for kk in range(2):
     if sa[kk]<0:ta=[x+y for x,y in zip(ta,sub(e(aa[kk]),e(ma)))]
     if sb[kk]<0:tb=[x+y for x,y in zip(tb,sub(e(bb[kk]),e(mb)))]
   global_rows.append((L,c,ca,cb))
   for j in range(4):
    s.add(L[j]+int(ma==0)*ca*A[j]==tb[j])
    s.add(L[j]+c*r[j]+int(mb==1)*cb*B[j]==ta[j])
  relu=lambda z:z3.If(z>=0,z,0)
  for x in ([1,1,0,0],[0,0,-1,0],[0,0,0,-1]):
   vals=[]
   for L,c,ca,cb in global_rows:
    vals.append(z3.Sum([L[j]*x[j] for j in range(4)])+c*max(0,sum(r[j]*x[j] for j in range(4)))+ca*relu(z3.Sum([A[j]*x[j] for j in range(4)]))+cb*relu(z3.Sum([B[j]*x[j] for j in range(4)])))
   s.add(vals[2]+relu(vals[0])+relu(vals[1])==max(x))
  all_cases.append(z3.And(*s.assertions()))
  res=s.check();rec={'ma':ma,'mb':mb,'swap':swap,'sa':sa,'sb':sb,'status':str(res)}
  if res==z3.sat:
   m=s.model();rec['u']=str(m.eval(u));rec['v']=str(m.eval(v));rec['global']={str(d):str(m[d]) for d in m.decls()}
  out.append(rec)
 result={'scope':'necessary exact local-germ model, all real firstnormal ratios, no global identity inferred fromSAT','count':len(out),'sat':sum(x['status']=='sat' for x in out),'cases':out,'seconds':time.monotonic()-t}
 combined=z3.SolverFor('QF_LRA');combined.add(z3.Or(*all_cases));HERE.joinpath('max5_exact_local4_one_root_germs.smt2').write_text('(set-logic QF_LRA)\n'+combined.sexpr()+'\n(check-sat)\n')
 HERE.joinpath('max5_exact_local4_one_root_germs.json').write_text(json.dumps(result,indent=2));print({k:v for k,v in result.items() if k!='cases'})
 for q in out:
  if q['status']=='sat':print(q)
if __name__=='__main__':main()
