#!/usr/bin/env python3
"""Exact diagonal-shuffle pole and split-channel product controls."""
from pathlib import Path
import hashlib,json
import sympy as sp

HERE=Path(__file__).parent


def main():
    x,y,a=sp.symbols('x y a')
    diagonal=(1/(y*(y-a))+1/(x*(x+a)))/(x+y)**2
    off=(1/(x*(y-a))+1/(y*(x+a)))/(x+y)**2
    target=1/(x*y*(x+a)*(y-a))
    assert sp.cancel(diagonal+off-target)==0
    diagonal_pole=sp.cancel(((x+y)**2*diagonal).subs(y,-x))
    off_pole=sp.cancel(((x+y)**2*off).subs(y,-x))
    assert diagonal_pole==2/(x*(a+x)) or sp.cancel(diagonal_pole-2/(x*(a+x)))==0
    assert sp.cancel(diagonal_pole+off_pole)==0
    alpha,beta,gamma,delta=sp.symbols('alpha beta gamma delta')
    F=lambda q,s,t:1/((q+s*a)*(q+t*a))
    left=F(x,alpha,beta)*F(y,gamma,delta)
    right=F(x+y,alpha+gamma,beta+delta)*(F(x,alpha,beta)+F(y,gamma,delta)
        +1/((x+alpha*a)*(y+delta*a))+1/((y+gamma*a)*(x+beta*a)))
    assert sp.cancel(left-right)==0
    result=dict(status='EXACT_DIAGONAL_BST_DOUBLE_POLE_AND_COUPLED_PRODUCT_IDENTITY',
                diagonal_double_pole_coefficient=str(diagonal_pole),
                off_diagonal_double_pole_coefficient=str(off_pole),
                concrete_double_pole_coefficient=str(diagonal_pole.subs({x:1,a:3})),
                product_rule='Four independent real/rational offsets; exact rational identity.',
                scope='Refutes same-extension diagonal grouping as a CPWL top kernel; does not exclude coupled BST states or a uniform construction.',
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE/'overnight_upper_bst_coupling.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':main()
