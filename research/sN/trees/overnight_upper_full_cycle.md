# Full-label cycle controls

These tests concern a new family with every label on the comparison cycle.
They do not reuse the omitted-apex canonical cycle obstruction. They are
finite research calculations, not a uniform construction or a Lean proof.

For `g_i=x_i-x_(i+1)` on a cycle, the atoms are

\[
\sigma\left(\sum_i h_i g_i+\sum_{i\in E}\sigma(g_i)\right),
\qquad h_i\in\mathbb Z,\quad \max h-\min h\le B.
\]

The head is unchanged by adding a common constant to its cyclic
coefficients. All edge subsets `E` are allowed in the state test.
Reversing the whole cycle sends `(h_i,E_i)` to
`(-h_{-i-1}-E_{-i-1},E_{-i-1})`, up to a cyclic shift and a common head
constant. This transformation is used only to identify equivalent atoms;
the complete bounded family is generated before quotienting.

The test uses full permutation sums, so every cycle order is present.
This is a necessary control for smaller exponentially sized cycle-order
families; it is not itself an exponential count. A complete chamber
decomposition collects every mixed-sign primitive kink normal and every
linear coefficient on the positive gap orthant. Exact rational rank of
this system decides membership of `N max(x)-sum_i x_i`, with an auxiliary
sum of pairwise absolute differences. The first producer independently
compares its gap profiles with direct evaluation of the original atoms.

| Family | Arity | Orbit columns | Exact ordinary / augmented rank |
|---|---:|---:|---:|
| Full edge set, head height at most 3 | 5 | 83 | 79 / 80 |
| All edge subsets, head height at most 2 | 5 | 956 | 216 / 216 |
| All edge subsets, head height at most 1 | 6 | 588 | 164 / 165 |
| All edge subsets, head height at most 2 | 6 | 5,266 | 1,220 / 1,221 |

The five-input positive solution uses only eight orbit sums, coefficients
with denominators at most 48, and heads of height at most one. Its edge
subsets have one, two, or three edges. It therefore does not demonstrate
that a genuinely cyclic atom is necessary or useful. The six-input
failures show that this particular small solution does not extend within
either tested alphabet.

The precise five-state scope needs care. Starting from a full cycle with
head height at most `B0`, replacing edges by either hinge orientation,
either linear orientation, or zero changes each head coefficient by an
element of `{-1,0,1}`. Its entire formal-state family is contained in the
all-subset test of head height at most `B0+2`. Thus the height-two
calculation does **not** exclude the full formal-state family of an
initial height-two head. Arbitrary real heads and arbitrary non-unit inner
weights are also outside these finite exclusions.

## The boundary state retained for further work

The full cycle base has rank `N-1`. A top visible facet can freeze two
cycle edges and leave two path components, rather than one omitted apex
and one tree. This is why the earlier cycle obstruction does not apply.

More generally let two rooted trees `P,Q` partition all labels, with roots
`r,s`, and consider an outer ReLU with head `h` and oriented inner tree
edges. Write

\[
a=\sum_{v\in Q}\omega_v,\qquad
c=\sum_{v\in P}h_v=-\sum_{v\in Q}h_v>0.
\]

For each root-away cut let `q_e` be its frequency sum, `H_e` its head sum,
and `epsilon_e` the sign of the hinge's endpoint in that cut. Independent
root-difference and edge-difference coordinates give the generic Fourier
kernel, in the existing tree normalization,

\[
(-a)^{N-4}c^{3-N}
\prod_e
\frac{1}{
 [q_e+(a/c)H_e]
 [q_e+(a/c)(H_e+\epsilon_e)]}.
\]

The derivation uses the head coordinate `t=x_r-x_s`, whose frequency is
`-a`; its integration contributes `c/a^2`, and every edge contributes a
factor with numerator `-a/c`. For a root-difference head, `c=1` and every
`H_e=0`, recovering the simpler relative kernel. When `c=0`, the atom is
constant along the relative component shift, so its generic top kernel
vanishes. This formula has been independently compared with the lower
agent's boundary-state derivation. A uniform spanning identity for such
states is still open.

Producers: `overnight_upper_full_cycle.py` and
`overnight_upper_full_cycle_states.py`. Each bounded run uses
`overnight_upper_run.py`, one thread, at most 3 GiB, and a 20-minute limit.
The height-two six-input test finished in 75.7 seconds with observed RSS
below 1.2 GiB. JSON receipts retain the complete exact integer systems and
producer hashes; they can also be regenerated from the small sources.
