# Factorial dimension: one wall, or one common germ

**Status:** written mathematical proof and audit of alternatives. The
independent proof agent reviewed the fixed-wall proof, including signed
weights, affine shallow remainders, the outside region, and N=3, and
found no gap. No Lean
or paper files were changed. The existing checked third-difference proof
remains intact. The fixed-wall proof below is the shortest independent
route found; the common-germ proof also works and unifies the exposition
with the counting lower bounds.

Put r=N-2>=1 and b=N-1. For a permutation pi of the middle labels,
write pi(r+1)=b and use the existing dictionary function

    U_pi(x) = sigma(x_b-x_0 + D_pi(x)),
    D_pi(x) = sum_(j=1)^r sigma(x_pi(j)-x_pi(j+1)).

There are r! such functions. Let S_N denote the span of linear functions
and sigma(ell(x)) for arbitrary linear forms ell. Thus S_N is the full
homogeneous shallow span in full coordinates, rather than only the
paper's auxiliary span A_N.

## 1. Recommended independent proof: disjoint crease patches on one wall

Fix H={x_0=x_b}. At p in H define the symmetric normal derivative

    J_H f(p) = lim_(t downarrow 0)
        [f(p+t e_0)+f(p-t e_0)-2f(p)]/t.

This exists for CPWL functions and is linear in f. Since D_pi does not
depend on x_0 and D_pi>=0,

    J_H U_pi(p) = 1 if D_pi(p)=0, and 0 otherwise.                 (1)

The zero condition means exactly

    x_pi(1) <= ... <= x_pi(r) <= x_b.

At points where the middle coordinates and x_b are distinct, (1) is
therefore the indicator of the open chamber

    C_pi = {p in H: p_pi(1)<...<p_pi(r)<p_b}.

These chambers are disjoint. There is also a nonempty open part of H
where all the indicators vanish: take any middle coordinate above p_b.

A shallow function has a **constant** value of J_H at generic points
of H. Indeed, a ReLU whose defining hyperplane is H contributes its
constant normal jump; every other defining hyperplane intersects H in
a proper affine hyperplane, outside which that ReLU is locally linear.
There are only finitely many exceptional hyperplanes.

Now suppose sum_pi a_pi U_pi is shallow. On an open part of H outside
all C_pi, choose a point avoiding those exceptional hyperplanes. Its
jump is zero, so the shallow function's generic jump constant is zero.
For each rho, choose a generic point in C_rho. Its jump is a_rho by
(1), hence a_rho=0. This proves independence modulo S_N.

This proof uses one hyperplane with disjoint crease patches, not a
different private hyperplane for each path. A single point on H would
not suffice: an auxiliary sigma(x_b-x_0) has the same jump there.
The outside open region is the essential additional observation.

### Compact exposition

> On H={x_0=x_b}, the normal derivative jump of U_pi is the indicator
> of x_pi(1)<...<x_pi(r)<x_b, away from coordinate ties. These chambers
> are disjoint, whereas every shallow function has constant jump at
> generic points of H. A shallow linear combination of the U_pi has
> jump zero where a middle coordinate exceeds x_b, so that constant
> is zero; evaluating on each chamber forces every coefficient to vanish.

The generic-point formulation does not choose points before seeing the
shallow relation. This is legitimate for proving independence. If fixed
scalar linear functionals are desired, average J_H over a small compact
ball in C_rho and subtract its average over a ball in the outside region.
Other shallow walls have measure zero in H, so these averages annihilate
S_N and give the identity evaluation matrix. Introducing integration is
unnecessary for the paper proof.

## 2. The common-germ route is valid and almost as short

For an order rho set c=rho(r). Choose p with

    p_0=p_b=p_c=0,
    p_rho(1)<...<p_rho(r-1)<0.

For example p_rho(j)=j-r works. For pi!=rho, the middle pi-order has a
strict descent in these heights. Hence D_pi(p)>0, so the outer ReLU is
locally linear. Its germ is a linear function plus comparison ReLUs,
and is shallow.

For the matching path, every inner comparison except the last is strictly
negative. Its germ, restricted to the tied labels T={0,b,c}, is

    sigma(v_b-v_0+sigma(v_c-v_b))
      = max(v_0,v_b,v_c)-v_0.                                  (2)

It is invariant under a common shift of the tied coordinates. Therefore
the second germ at the all-ones tied direction in the paper's common
test does not change (2). After setting v_0=0, its class is the nonzero
triangle support function max(0,v_b,v_c) modulo L_1. Every other path
and every shallow remainder maps to zero. Applying this test for each
rho gives the independence assertion immediately.

There is no issue at N=3: there is one path, the outside set is empty
for the germ test, and (2) is the same nonshallow triangle. The wall
proof also works because its inside and outside regions are nonempty.
N=2 would fail: there are no middle labels, and the path unit is shallow.

### Compact exposition reusing the common-test lemma

> For each rho, tie 0,b,rho(r) at the top and place the other middle
> labels in strict rho-order below them. The matching path has germ
> max(v_0,v_b,v_rho(r))-v_0; every other path has a positive outer
> preactivation and therefore a shallow germ. The common tied-maximum
> test sends these paths to a diagonal family of nonzero triangle
> classes, proving their independence modulo the shallow span.

This is a direct replacement for the paper exposition if reuse of the
common-germ lemma is the main objective. The wall proof instead gives
a self-contained argument without another simplex nonvanishing lemma.

If the common lemma is replaced by its generic-stratum one-germ version,
raise every base coordinate by one, so the top tie has height one. The
selected path functions are invariant under common translation, so the
same germs result. They already have zero common tied slope; the second
germ is unnecessary. This gives exactly the same diagonal argument with
the new single-germ counting test.

## 3. The ambient quotient and the genuine strengthening

The conclusion is

    dim(V_N / (V_N intersect S_N)) >= (N-2)!.

Since A_N is contained in V_N intersect S_N, this implies the existing
q_N=dim(V_N/A_N)>=(N-2)!. One must use the intersection: S_N is generally
not a subspace of the finite dictionary span V_N.

The same independence holds after restricting to H_0={x_0=0}, modulo
the paper's full L_1(H_0). Indeed, any shallow relation on H_0 extends
to full coordinates by x -> x-x_0 1; this preserves shallowness and
fixes all the path functions. The wall proof also allows arbitrary
finite affine shallow remainders, including biases, because their other
walls still meet H only in proper affine hyperplanes.

Neither proof establishes independence modulo L_(N-2). For N>=4, the
function max(x_0,x_b,x_c) itself lies in L_2, hence in L_(N-2), while
its tied-triple test is nonzero. Thus this test does not descend to that
larger quotient. This is an explicit obstruction to that inference,
not a claim that independence in the larger quotient has been disproved.

The factorial dictionary dimension also remains distinct from the
number of units needed to represent the one target max_N. It does not
exclude an exponential construction tailored to that target.

## 4. Robust extension to weighted paths

The fixed-wall proof extends to

    W_pi(x) = sigma(beta_pi (x_b-x_0)
              + sum_j a_pi,j sigma(x_pi(j)-x_pi(j+1))),

where beta_pi and every a_pi,j are arbitrary nonzero real numbers,
chosen separately for every path. Positive edge weights give (1)
directly, with jump |beta_pi|. Signed weights require one extra
generic-point observation.

On any fixed strict order chamber of H, the weighted inner sum is a
linear combination of its active path-edge forms. These forms are
linearly independent: they are the incidence vectors of a path on
the N-1 tree labels, and restriction to H leaves those tree coordinates
free. Thus a nonempty active set gives a nonzero linear form, whose
zero set is a proper hyperplane in H. Avoid these finitely many extra
hyperplanes. The inner sum then vanishes exactly in C_pi, where no
comparison is active. Consequently the generic jump is |beta_pi| on
C_pi and zero elsewhere. The same argument proves factorial
independence modulo the entire shallow span.

This is a family-dimension theorem for the weighted functions. It does
not assert that arbitrary weighted functions belong to the original
caterpillar dictionary. Nonzero weights are necessary for this proof:
zero edges remove ordering constraints, and beta_pi=0 removes the
selected normal crease.

## 5. Comparison with the current third mixed difference

The existing eight-corner proof has an excellent finite certificate:
fixed evaluation points, an explicit identity matrix, and an existing
Lean verification. It annihilates every function of at most two
coordinates, even beyond the shallow class. Its test does not
annihilate arbitrary shallow directions, such as
sigma(x_0+x_b+x_c), so its stated auxiliary quotient is natural.

The germ and wall proofs give a different, stronger conclusion for
the relevant full shallow quotient. The common-germ route best unifies
the paper's lower-bound methods. The fixed-wall route is the shortest
standalone explanation and adds the arbitrary signed-weight extension.
The existing Lean route should remain until any replacement has been
checked at the same formal level.
