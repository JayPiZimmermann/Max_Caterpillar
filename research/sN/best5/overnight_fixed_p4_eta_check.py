"""Independent five-point contradiction to the single-eta P4 extension."""
from fractions import Fraction as Q
import hashlib,json
from pathlib import Path

points=((4,4,2,-1),(4,4,2,0),(4,4,2,1),(0,3,4,5),(0,3,4,6));coeff=(1,-2,1,1,-1);required=(-2,-2,-2,2,3);rows=[];details=[]
for x,eta in zip(points,required):
    u,v,s,t=map(Q,x);a,b,c,d=(max(0,z)for z in(u,v,s,t));S=a+b;T=c+d;D=abs(a-b);E=abs(c-d);k=(T-S)/2;base=(S+max(D,E))/2;change=max(a,b,c,d)-base
    if k>0:assert 0<change<k and eta==change
    else:assert k<change<0 and eta==k-change
    z=[max(Q(0),v)for v in(u,v,v-u,s,t,s-t,v-t)];rows.append(z);details.append({'point':x,'features':list(map(str,z)),'k':str(k),'target_minus_base':str(change),'forced_eta':eta})
assert all(sum(c*r[j]for c,r in zip(coeff,rows))==0 for j in range(7))
assert sum(c*eta for c,eta in zip(coeff,required))==-1
report={'status':'PASS_EXACT_FIVE_POINT_LINEAR_ETA_OBSTRUCTION','points':details,'relation_coefficients':coeff,'feature_relation':[0]*7,'forced_eta_relation':-1,'scope':'Only the known four-free-term identity with a freely chosen single linear comparison argument eta; other four-term P4 architectures are not excluded.','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};p=Path('research/sN/best5/overnight_fixed_p4_eta_check.json');p.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
