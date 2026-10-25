"""Exact positive control: known12-free-term network satisfies all49 equations."""
from fractions import Fraction as Q
from pathlib import Path
import json,hashlib,time
import overnight_root9_equations as E
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();E.initialize();a=E.arithmetic;np=HERE/'overnight_fixed_cross_net9_14_simple.json';net=json.loads(np.read_text());zs=[];ds=[];theta=[]
    for row,d0 in zip(net['second_layer'][2:],net['output'][2:]):
        row=list(map(Q,row));d=Q(d0);assert d and row[-2:]==[0,0];g=[abs(d)*Q(v)for v in row[:7]];z=sum(1<<i for i,S in enumerate(a.REL)if sum(x*y for x,y in zip(g,a.VALUE[S]))==0);B=a.BASES[z];dim=len(B);rows=a.rref([[B[k][j]for k in range(dim)]+[g[j]]for j in range(7)]);assert len(rows)==dim;sol=[Q(0)]*dim
        for row in rows:
            p=next(i for i,c in enumerate(row)if c);assert p<dim;sol[p]=row[-1]
        assert all(sum(sol[k]*B[k][j]for k in range(dim))==g[j]for j in range(7));zs.append(z);ds.append(1 if d>0 else-1);theta+=sol
    eq,forms,_=E.case_data(zs,ds);av=[abs(sum(x*y for x,y in zip(f,theta)))for f in forms]
    for i in range(49):
        co,rhs=eq(i);assert sum(c*av[j]for j,c in co.items())==rhs,(i,co,rhs)
    report={'status':'KNOWN_NINE_BY_FOURTEEN_ALL49_EQUATIONS_PASS','free_terms':len(zs),'equations':49,'seconds':time.monotonic()-start,'network_sha256':hashlib.sha256(np.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exact arithmetic positive control of the necessary equation model; global equality is independently certified by overnight_fixed_cross_verify.py.'};(HERE/'overnight_fixed_p4_k4_control.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)
if __name__=='__main__':main()
