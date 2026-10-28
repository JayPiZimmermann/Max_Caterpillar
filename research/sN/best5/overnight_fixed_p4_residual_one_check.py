from fractions import Fraction as Q
from pathlib import Path
import json,hashlib


def main():
    relu=lambda x:max(x,Q(0));points=[Q(i,2)for i in range(1,6)];values=[];table=[]
    for rho in points:
        u,v,s,t=Q(2),-rho,-2*rho,-3*rho;a,b,c,d=map(relu,(u,v,s,t));p,q,r=relu(v-u),relu(s-t),relu(v-t);assert u>0>v>s>t and[a,b,c,d,p,q,r]==[2,0,0,0,0,rho,2*rho];L=d+q-a-p;M=L+(a+b-c-d)/2;assert(L,M,b-a+d-c,b-a+c-d)==(rho-2,rho-1,-2,-2);G=a+relu(L)-relu(M)+(relu(b-a+d-c)+relu(b-a+c-d))/2;E=max(Q(0),u,v,s,t)-G;assert E==relu(rho-1)-relu(rho-2);values.append(E);table.append([str(rho),str(E)])
    differences=[values[j]-2*values[j+1]+values[j+2]for j in range(3)];assert differences==[Q(1,2),0,Q(-1,2)];report={'status':'EXACT_SINGLE_RELU_RESIDUAL_REPAIR_REFUTED','table':table,'second_differences':list(map(str,differences)),'scope':'Only the specified fixed four-term formula plus arbitrary linear remainder and one signed outer ReLU in all seven P4 features. General five-term construction remains open.','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path(__file__).with_suffix('.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True))
if __name__=='__main__':main()
