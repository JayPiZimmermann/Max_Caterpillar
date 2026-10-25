#!/usr/bin/env python3
"""Exact polynomial controls for logarithmic transfer and cutoff obstruction."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,math
HERE=Path(__file__).parent

def mul(a,b):
    result=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):result[i+j]+=x*y
    return result

def main():
    differences=[]
    for m in range(13):
        total=[0]*(m+1)
        for j in range(m+1):
            polynomial=[1]
            for k in range(m+2):
                if k not in (j,j+1):polynomial=mul(polynomial,[-k,1])
            coefficient=(-1)**(m-j)*math.comb(m,j)
            for i,c in enumerate(polynomial):total[i]+=coefficient*c
        assert total==[math.factorial(m+1)]+[0]*m
        differences.append(dict(order=m,cleared_numerator=total[0],denominator_roots=list(range(m+2))))
    defects=[]
    for L in range(1,13):
        # P_L(z)=sum_(r=1)^L (-1)^(r-1)(z-1)^r/r.
        polynomial=defaultdict(Q)
        for r in range(1,L+1):
            for k in range(r+1):polynomial[k]+=Q((-1)**(r-1+r-k)*math.comb(r,k),r)
        defect=defaultdict(Q)
        for k,c in polynomial.items():
            defect[(k,-k)]+=c;defect[(k,0)]-=c;defect[(0,k)]+=c
        defect={k:c for k,c in defect.items() if c}
        expected=Q((-1)**(L-1),L)
        assert defect[(L,-L)]==expected
        defects.append(dict(log_degree=L,witness_monomial=[L,-L],coefficient=str(expected),terms=len(defect)))
    result=dict(status='EXACT_LOGARITHMIC_CUTOFF_CONTROLS_PASSED',translation_differences=differences,
        truncated_log_defects=defects,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Finite controls of two displayed uniform elementary identities. No finite logarithmic chain or exponential network construction is asserted.')
    (HERE/'overnight_upper_logarithmic_states.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'DIFFERENCE_ORDERS',len(differences),'LOG_DEGREES',len(defects))

if __name__=='__main__':main()
