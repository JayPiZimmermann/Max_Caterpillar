# A marked two-component kernel algebra

25 October 2026. The formulas and the head-exchange identity below are
uniform algebraic statements. The seven-label separation test is modular.
No unrestricted all-tree exponential lower bound follows yet.

## States and their actual Fourier kernels

Partition all `N` labels into two tree components `P,Q`, root them at
`r in P,s in Q`, and take the head `x_r-x_s`. Keep every inner edge as
an oriented positive ReLU; there are `N-2` such edges. On `sum omega=0`, put

```
a = sum_(v in Q) omega_v = -sum_(v in P) omega_v.
```

For each inner edge, `q_e` is its cut sum away from its component root,
and `epsilon_e=+` when its positive endpoint is away from that root. Then

```
R = (-a)^(N-4) product_e 1/[q_e(q_e+epsilon_e a)].       (1)
```

The usual canonical tree unit has `Q` a singleton. Formula (1) follows by
using the head coordinate `t=x_r-x_s` and the independent edge differences.
The Fourier frequency of `t` is `-a`. Integrating the outer ReLU gives the
usual second-order head denominator; each inner edge contributes the same
factor `-a/[q_e(q_e+epsilon_e a)]` as in the canonical calculation. The
augmented tree consisting of the head and inner edges is a unimodular
coordinate basis, so there is no additional determinant magnitude.

There is an independent basis-matrix formulation. Put all the head and
oriented inner edge forms into a matrix on any coordinate chart. Let their
dual frequency coordinates be `lambda_0,lambda_1,...,lambda_(N-2)`, with
index0 the head. Then

```
R = lambda_0^(N-4)
    / product_(i>=1) lambda_i(lambda_i-lambda_0).        (2)
```

This avoids rooted cut bookkeeping entirely.

For a general balanced head `h`, let `c=sum_P h=-sum_Q h`; rename the
components so `c>0`. If `H_e` is the sum of `h` on the root-away edge cut,
replace each factor in (1) by

```
[q_e+(a/c)H_e] [q_e+(a/c)(H_e+epsilon_e)]
```

and multiply the numerator by `c^(3-N)`. If `c=0`, the function is invariant
under the relative component shift and its generic top kernel is zero.
The minimal algebra tested below uses only the pure root-difference head,
so `c=1` and every `H_e=0`. Arbitrary cut shifts are a separate enlargement.

## Product law with both external charges retained

Put `p=|P|`, `q=|Q|`, and retain `a=sum_Q omega`. Let `R_P` be the canonical
kernel on `P` with an external apex of frequency `a`. Let `R_Q` be the
canonical kernel on `Q` with external apex frequency `-a`, reversing every
inner orientation in `Q`. Directly from (1),

```
R_(P,Q) = (-1)^(q-1) a^2 R_P R_Q.
```

The target kernels obey the compatible identity

```
R_max,N = a^2 R_max,p+1(omega_P,a) R_max,q+1(omega_Q,-a).
```

These formulas are rational identities, including singleton components.
They do not imply that either factor can be expanded using a fixed external
apex. Such fixed-apex sufficiency fails from four labels onward by coordinate
deletion: its atoms become shallow when that apex is removed, whereas the
maximum remains nonzero in the lower top quotient. Moving a factor's apex
into the other component therefore has to remain explicit in any gluing
argument. The scalar relative obstruction recorded separately also shows
that collapsing the attachment information before gluing loses too much.

## Grafting is a genuine linear operation on marked kernels

Attach a new leaf `y` to a marked vertex `h`, with relative edge sign
`epsilon`. Absorb its frequency into `h` in the old kernel. The resulting
kernel is

```
G_(h,epsilon) F = -a/[omega_y(omega_y+epsilon a)]
                 * F(...,omega_h+omega_y,...).          (3)
```

Here `a` is the total frequency of the updated marked negative component.
If the graft is in `P`, that total is unchanged. If it is in `Q`, the
substitution into the old marked state makes its old total equal the new
one. All old cut sums and the ratio of prefactors agree directly, proving
(3). Consequently any rational identity among states with the same marked
component structure is preserved by grafting. This includes grafting at
the actual apex, provided its component is retained as a two-root state
instead of being discarded.

For a fixed singleton apex, a fixed-apex `S_4` identity at five labels can
therefore be lifted to nine labels by adding a leaf at every nonapex vertex.
After full symmetrization, each summand is the corresponding tree corona.
All these coronas have a perfect matching. The sparse signed-root candidate
passes the exact *finite source relation* tests for all five counts of
outward/inward corona leaves, and all16 orientations of a four-edge path
averaged over its old attachment vertex. This is a useful necessary check,
not a proof of all rational identities. The source matrix has rank16;
its24 exact rows are preserved in the producer receipt. An initial SymPy
elimination was stopped after69 seconds; FLINT completed the gate in under
one second. Files: `overnight_uniform_pruning_generator_gate*`.

## A uniform head-exchange identity, including its corrections

Fix `m=N-1` oriented edge forms `t_1,...,t_m` of one augmented tree. For each
nonempty set `I`, put

```
U_I = sigma(sum_(i in I) t_i + sum_(j not in I) sigma(t_j)).
```

Then the exact identity is

```
sum_(empty!=I subset[m]) (-1)^(|I|+1) U_I
    = sum_j sigma(t_j).                                (4)
```

A direct proof is shortest. Include `I=empty` in the alternating sum. If
some `t_k>=0`, pair `I` with `I symmetric_difference {k}`: moving `t_k`
between the linear and ReLU sums changes nothing, so the terms cancel.
If every `t_k<0`, all summands vanish. The empty summand is
`sum_j sigma(t_j)`, which gives (4). No independence assumption is required
for this identity.

For the quotient conclusion assume `m>=2`. Each `|I|>=2` term depends on at most `m-|I|+1<=m-1` linear forms. Thus
modulo `L_(m-1)`, the sum of all single-head choices is zero. The corrections
are explicit states with several edges absorbed into the head.
Geometrically, the single-head polytopes are the pyramids from0 to the
coordinate facets of `[0,1]^m`; they cover the cube according to which
coordinate is maximal. Their intersections give precisely the `I` terms.

The same statement has a one-line rational proof. Choose a fixed global
root of the augmented tree, let `q_e` be its independent cut-flow
coordinates, and set `z_e=epsilon_e q_e`, where `epsilon_e` describes the
fixed oriented edge. If edge `H` is selected as the head with that same
orientation, (2) is

```
R_H = (-1)^(m-1) z_H^(m-2)
      / [(product_e z_e) P'(z_H)],
P(t)=product_e(t-z_e).
```

The sum over `H` is zero by Lagrange interpolation, since the numerator
polynomial has degree `m-2<m-1`. This proves that the entire head sum has
zero generic Fourier kernel without choosing or discarding an apex.

## Matching interpretation of the states

For odd `N=2q+1`, call a state deficient when its inner two-component forest
has matching number at most `q-1`. The canonical case is exactly a
non-perfect-matchable tree plus its isolated apex. For an augmented tree
with matching number `q`, a head edge is deficient precisely when it
belongs to every maximum matching: deleting that edge lowers the maximum
matching number. If the augmented tree itself has matching number below
`q`, every head choice is deficient.

This interpretation explains a constraint on proposed separators. They
must vanish on the essential-head states, while their values on all head
choices of a fixed oriented augmented tree must sum to zero by (4). Merely
assigning a positive determinant score to every nondeficient state cannot
satisfy those relations in general.

## Bounded seven-label diagnostic

At seven labels, beyond the canonical258 deficient rooted/oriented tree
orbits, the only additional deficient two-component shapes are

- an edge together with a five-vertex star;
- a three-vertex path together with a four-vertex star.

They give26 and70 rooted/oriented types respectively. Naming the smaller
component first loses no span: swapping the head components and reversing
all inner edge orientations negates the kernel at odd arity.

The full `S_7` evaluation gate on these354 columns gives modular ranks
`129/130`, with the target independent. The rank is stable from160 through
320 rows, modulo1000003. Compilation and evaluation together took5 seconds,
using one thread. All permutation multiplicities are retained.

`overnight_uniform_pruning_biforest_check.*` independently recomputes twelve
entries exactly using (2), inverting the complete unimodular head/hinge
basis instead of using graph cuts. Those controls pass. They check the
new evaluator; they do not turn the modular rank into an exact separator.
The producer, C++ evaluator, data, and log are
`overnight_uniform_pruning_biforest*`; the binary caches are reproducible.

## Exact remaining issue

The two-component state algebra keeps the external apex/attachment data
needed by gluing. Grafting and head exchange are now honest operations and
relations, with explicit correction states. But a common linear functional
on the unmarked rational-function space still has to respect relations
between different marked partitions and different augmented tree bases.
The finite signed-root scores and the new modular gate do not establish
that descent. Tensorizing the exact seven-label separator would require a
relative version that controls those relations and retains a nonzero
response on `1/product omega_i`; that step remains open.
