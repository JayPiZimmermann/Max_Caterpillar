# The sparse signed-root score fails an exact local relation at nine labels

The proposed score \(Q_*\) does **not** descend to a linear functional on
the actual Fourier rational functions. This closes that particular formula;
it does not refute a uniform perfect-matching separator or an exponential
lower bound for unrestricted tree dictionaries.

The final proof uses six individual kernels, with no sampled rank
assumption and no need to sum over apex positions.

## Exact six-term obstruction

Every tree has root \(1\), apex \(0\), and the five common oriented edges

\[
 (5,2),\ (2,7),\ (4,3),\ (6,5),\ (7,8).
\]

The convention \((u,v)\) means the summand \(\sigma(x_u-x_v)\).
Add the following two edges:

| Term | Added edges | Coefficient | \(Q_*\) |
|---|---|---:|---:|
| 1 | \((2,1),(1,3)\) | \(+1\) | \(3300\) |
| 2 | \((1,2),(3,1)\) | \(-1\) | \(300\) |
| 3 | \((3,1),(2,3)\) | \(-1\) | \(0\) |
| 4 | \((2,1),(3,2)\) | \(+1\) | \(660\) |
| 5 | \((1,3),(3,2)\) | \(+1\) | \(0\) |
| 6 | \((1,2),(2,3)\) | \(-1\) | \(3900\) |

Put \(a=\omega_0\),
\(x=\omega_2+\omega_5+\omega_6+\omega_7+\omega_8\),
\(y=\omega_3+\omega_4\), and
\(f_\epsilon(q)=1/[q(q+\epsilon a)]\).
The six kernels share their factor \((-a)^5\) and all five factors from
the common edges. The remaining factors are, in table order,

\[
\begin{gathered}
 f_+(x)f_-(y),\quad f_-(x)f_+(y),\\
 f_+(x+y)f_+(x),\quad f_+(x+y)f_+(y),\\
 f_-(x+y)f_-(x),\quad f_-(x+y)f_-(y).
\end{gathered}
\]

They satisfy the rational identity

\[
 f_+(x)f_-(y)-f_-(x)f_+(y)
 =
 f_+(x+y)\bigl(f_+(x)-f_+(y)\bigr)
 -
 f_-(x+y)\bigl(f_-(x)-f_-(y)\bigr).
\]

The common-edge cut factors remain unchanged when a branch is reattached
through its original root \(2\) or \(3\). Therefore the six individual
Fourier kernels have weighted sum zero at every generic frequency, and so
do their unaveraged full label sums. Their proposed scores instead sum to
\(3300-300+660-3900=-240\).

The scalar identity was independently obtained in
overnight_upper_interval_local.py. The upper construction reviewer also
independently checked the branch attachment, cut signs, and shared
prefactor for this counterexample.

## Independent exact verification

overnight_uniform_q9_local_verify.py uses Python's standard library only.
It imports neither the score routine nor the modular producer. It:

1. multiplies the scalar identity by a common denominator and checks that
   every integer polynomial coefficient vanishes;
2. derives all rooted cuts directly from the six displayed trees and
   checks the common and variable factors;
3. enumerates all \(8!\) orders for each tree, counting signed connected
   prefix orders separately for every possible root;
4. evaluates the stated \(Q_*\) formula from these independent counts and
   obtains exactly the six values and the discrepancy \(-240\).

The receipt is overnight_uniform_q9_local_verify.json. The checker takes
under one second. Generic-frequency qualification only excludes denominator
hyperplanes; the identity is an identity of rational functions.

## How the necessary gate located the failure

The full nine-label inventory contains 9498 root/orientation orbits.
The exact identity

\[
 U=\sigma\left(\sum_v\kappa_vx_v
       -\sum_{\{u,v\}\in E(T)}\min(x_u,x_v)-x_0\right),
 \qquad \kappa_v=\operatorname{outdeg}(v)+1_{\{v=r\}},
\]

reduces them to 5450 whole-function classes: 3822 trees without a perfect
matching and 1628 with a perfect matching. The complete raw-to-class map
is saved in overnight_uniform_q9_quotient.json; these identifications are
analytic, independently of the sampled rows.

At 2112 modular evaluation rows, each of the five perfectly matchable
tree shapes separately remained compatible with \(Q_*\). Their union,
together with stars and the target, had rank 1260 and yielded a twelve-term
candidate relation with coefficients \(\pm1\) and score discrepancy \(180\).
That sampled relation has not been promoted to an all-frequency identity.
It only selected a tree on which the exact six-term test above fails.
No further full matrix rows are needed or being generated.

The larger full matrix still had row rank 2112. Thus its failure to contain
the score row was underdetermined, and is not part of the proof.
Sampled proportional-column compression likewise remains diagnostic;
the actual gate used the exact \(\kappa\)-quotient.

The earlier five- and seven-label controls and the fixed-apex graft controls
remain valid observations at their stated scopes. They did not test this
nine-label local relation.
