import sys; sys.argv=['x','6']
exec(open('star_linear_full.py').read().split('target =')[0])
def show(c,s,T):
    for TT,rho,p in locs:
        if TT==T: print(c,s,T,rho,Lam(star(c,s),T,p))
show(4,{0:1,1:1,2:-1,3:-1,5:0},(0,1,2,3))
show(4,{0:1,1:1,2:-1,3:-1,5:1},(0,1,2,3))
