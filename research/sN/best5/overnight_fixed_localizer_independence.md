# A full-cone obstruction for individually localized four-hinge blocks

This is a proved restricted-family obstruction. It does not yet exclude
arbitrary shallow completions of the natural eight-row first layer.

Use the notation of `overnight_fixed_rayplane_obstruction.md`:

```
X=b-a, Y=d-c, h1=b+p-a, h2=d+q-c,
g_rs=X-Y+r*p+s*q,
P_rs=-sigma(g_rs)+sigma(g_rs-h1)
     +sigma(g_rs+h2)-sigma(g_rs-h1+h2).
```

For every real `r<=0,s>=0`, the function P_rs vanishes on the mixed
products B×C and C×B and on any product involving face A. On B×B it
equals `min(X,Y)`. Thus each block has the correct localized behavior
except for its unwanted contribution on C×C.

**Claim.** The restrictions of the P_rs to the interior of C×C are
linearly independent modulo linear functions. In particular, no finite
signed combination of these blocks cancels all their C×C contributions
while retaining a nonzero B×B crease.

**Proof.** On C×C write

```
b=d=0, p=a+x, q=c+y,       a,c,x,y>0.
```

In these four independent positive variables, the four ReLU normals of
P_rs are

```
(r-1,s+1,r,s),      (r-1,s+1,r-1,s),
(r-1,s+1,r,s+1),    (r-1,s+1,r-1,s+1).
```

Their first two coordinates have opposite signs because `r<=0,s>=0`.
Every one of these hyperplanes therefore intersects the interior of
the positive four-dimensional orthant.

Normalize each normal by its positive second coordinate `s+1`, and set

```
t=(1-r)/(s+1)>0,    k=1/(s+1)>0.
```

The first two coordinates are now `(-t,1)`. The last two coordinates
are respectively

```
(-t+k,1-k),    (-t,1-k),    (-t+k,1),    (-t,1).
```

The first normal is unique to this block. It cannot coincide with an
edge or base normal of any other block: its third coordinate is
strictly greater than `-t`, and its fourth is strictly less than one.
Two first normals coincide only if both t and k agree, which determines
r and s uniquely. Normalization by the positive second coordinate also
excludes an unnoticed negative proportionality.

After merging duplicate parameter pairs in a finite linear combination,
choose any block with nonzero coefficient. Its first hyperplane has a
nonempty relatively open part inside the positive orthant avoiding all
other hyperplanes. Across that part, this block produces a nonzero
gradient jump, and no other summand or linear function can cancel it.
This proves the claim.

Since all blocks have the same nonzero B×B crease, reproducing the
localized interaction there requires a nonzero sum of their coefficients.
The claim rules out cancellation on C×C. Adding an arbitrary linear
remainder does not change this contradiction.

## Remaining gap to an unrestricted all-width theorem

An arbitrary shallow completion may cancel unwanted mixed-face creases
collectively, using blocks that do not vanish on those faces individually.
The present proof does not establish a normal form reducing every such
completion to the family above. A finite cancellation-cycle or support
extremum argument must account for those additional transfers. The
sixteen ray-plane tests alone cannot supply that argument, as the exact
counterexample in `overnight_fixed_rayplane_obstruction.md` demonstrates.
