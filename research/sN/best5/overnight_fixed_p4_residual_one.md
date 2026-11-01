# A single outer ReLU cannot repair the failed four-term P4 formula

This is a precise failure of one construction route, not a lower bound
for five arbitrary free terms.

Write `a=σ(u)`, `b=σ(v)`, `c=σ(s)`, `d=σ(t)`,
`p=σ(v-u)`, `q=σ(s-t)`, `r=σ(v-t)`, and

```
L=d+q-a-p,    M=L+(a+b-c-d)/2,
G=a+σ(L)-σ(M)+(σ(b-a+d-c)+σ(b-a+c-d))/2.
```

Let `E=max(0,u,v,s,t)-G`. There do not exist arbitrary real linear
combinations R,g of all seven P4 features and a sign d0 in {+1,-1} with
`E=R+d0 σ(g)` globally. Allowing an additional affine constant does not
help this route.

Indeed take

```
(u,v,s,t)=(2,-rho,-2rho,-3rho),   rho>0.
```

This line stays in the strict braid cone `u>0>v>s>t`. Its feature vector,
in the order `(a,b,c,d,p,q,r)`, is `(2,0,0,0,0,rho,2rho)`. Hence
`L=rho-2`, `M=rho-1`, both fixed half-weight arguments are `-2`, and

```
E(rho)=σ(rho-1)-σ(rho-2).
```

Every candidate R and g restricts to an affine function of rho. Thus
`R+d0 σ(g)` is convex when d0 is positive and concave when d0 is negative.
The displayed E is neither: at rho=(1/2,1,3/2,2,5/2) its values are
`(0,0,1/2,1,1)`, whose consecutive second differences are `(1/2,0,-1/2)`.
Equivalently E has two distinct breakpoints, while a single affine ReLU
plus an affine remainder has at most one. This is a full-cone obstruction;
the five rational points merely provide a compact exact convexity witness.

The adjacent standard-library checker verifies the feature, preactivation,
output, and second-difference calculations in rational arithmetic. Other
five-term formulas, in which the existing four terms change together,
remain open. The next matching construction target is `(9,7)`.
