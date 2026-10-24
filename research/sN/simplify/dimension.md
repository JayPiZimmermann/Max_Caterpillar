# The dimension bound q_N >= (N-2)!: a shorter proof

Setting: N >= 3, r = N - 2, b = N - 1, x = (x_0, ..., x_{N-1}).
A_N = span{σ(x_i), σ(-x_i), σ(x_i - x_j)}, V_N = span of the dictionary,
q_N = dim(V_N / A_N).

## Theorem

q_N >= (N-2)!.

## Proof (third mixed difference)

**Units.** For each order ρ = (ρ(1), ..., ρ(r)) of the middle labels
1, ..., r, put ρ(r+1) := b. The caterpillar description (ρ with apex 0, all
cuts) gives the path unit

    U_ρ(x) = σ( x_b - x_0 + Σ_{j=1}^{r} σ(x_{ρ(j)} - x_{ρ(j+1)}) )  ∈ V_N.

**Detector.** For a coordinate e let (D_e g)(x) = g(x + e_e) - g(x). For
three distinct coordinates a, b, c and a point z let
Λ g = (D_a D_b D_c g)(z), a signed sum of g over the 8 corners z + ε,
ε ∈ {0,1}^{a,b,c}.

*Fact 1.* If g does not depend on one of x_a, x_b, x_c, then Λ g = 0.
(The D_e commute; D_e g = 0 if g does not depend on x_e.)
Hence Λ vanishes on every function of at most two coordinates, in particular
on all of A_N.

*Fact 2.* Λ g depends only on g restricted to the box z <= x <= z + 1.

For an order ρ let c = ρ(r) (the last middle label), and let z = z^ρ be
z_0 = z_b = 2r, z_{ρ(k)} = 2k (1 <= k <= r); so z_0 = z_b = z_c = 2r.
Put Λ_ρ = third mixed difference in x_0, x_b, x_c at z^ρ.

**Diagonal.** On the box, every hinge σ(x_{ρ(j)} - x_{ρ(j+1)}) with j < r is
0 (its argument is <= 2j - 2(j+1) + 1 = -1), so
U_ρ = σ(x_b - x_0 + σ(x_c - x_b)). With u = x - z on the three moving
coordinates, this is σ(u_b - u_0 + σ(u_c - u_b)) = [u_0 = 0 and
(u_b, u_c) ≠ (0,0)] at the corners, and the signed sum is
(+1) + (+1) + (-1) = 1. So Λ_ρ U_ρ = 1.

**Off-diagonal.** Let π ≠ ρ. Then ρ^{-1}π fixes 0 and is not the identity,
so it has a descent at consecutive path positions: a hinge
σ(x_p - x_q) of U_π with z_p - z_q >= 2 (both p, q middle labels). On the box,
x_p - x_q >= 1 and x_b - x_0 >= -1, so the outer argument of U_π is >= 0 and
U_π = (x_b - x_0) + Σ_j σ(x_{π(j)} - x_{π(j+1)}) there: a sum of functions
of at most two coordinates. By Facts 1 and 2, Λ_ρ U_π = 0.

**Conclusion.** If Σ_π c_π U_π ∈ A_N, applying Λ_ρ gives c_ρ = 0. The
(N-2)! units are independent modulo A_N. ∎

### Self-check

* Fact 1 for each auxiliary function: σ(±x_i) misses two of the three
  coordinates, σ(x_i - x_j) misses at least one, since {0, b, c} has three
  elements. No configuration analysis of auxiliary kinks is needed.
* Diagonal corner table (u_0, u_b, u_c) ↦ value, sign (-1)^{3-|ε|}:
  (0,1,0) ↦ 1 (+), (0,0,1) ↦ σ(0 + 1) = 1 (+), (0,1,1) ↦ σ(1 + 0) = 1 (-),
  every other corner 0 (u_0 = 1 gives σ(≤ 0) = 0; (0,0,0) gives 0). Sum 1.
  The hinge into c: σ(x_{ρ(r-1)} - x_c) <= σ(2(r-1) + 1 - 2r) = 0. ✓
* Off-diagonal: the descent cannot end at b, because z_b = 2r is maximal
  and ρ^{-1}π(b) = b is the largest position; so both ends of the descent
  hinge are middle labels with values 2·(position). ✓
* N = 3 (r = 1): one unit σ(x_2 - x_0 + σ(x_1 - x_2)), c = 1,
  Λ = D_0 D_2 D_1 at z = (2,2,2): value 1. ✓
* Numerically (lam.py, apex-0 detectors with fixed b): the
  (N-2)! × (N-2)! matrix (exactly the Lean point, step 1) is the identity for N = 3..7 (check_diag.py).

### Comparison with the previous proof (LowerBound.lean)

Old: symmetric second difference in x_0 at a test line minus a reference
line; needs ε-separation of all coordinates from x_b, a case analysis of the
kinks of σ(±x_i), σ(x_i - x_j) on both lines, and the reference configuration
to cancel σ(x_0 - x_b). New: one point, one functional; A_N is killed by
"depends on at most two coordinates" (the same principle as in the count
theorem); no reference line, no separation hypothesis.

## Can the same argument give more?

Checked numerically with exact integer evaluations and rank mod p
(scripts in this folder):

* All-hinge path units (apex a, path through the other labels) satisfy
  U(path) = U(reversed path), so there are N!/2 of them; their rank modulo
  A_N is 12/12 (N=4), 55/60 (N=5). With fixed apex 0: 3/3, 11/12. So
  neither (N-1)!/2 (fixed apex) nor N!/2 (all paths) is an independent
  family of path units.
* The third-difference detectors at "three tied top labels" points depend
  only on (the 3-set T, the order of the rest): N!/6 of them, and on path
  units they have rank exactly N!/6 for N = 4, 5, 6 (4, 20, 120). So path
  units + these detectors could prove at most q_N >= N!/6, but no uniform
  diagonal/triangular choice exists: the natural "monotone" choice
  (apex ∈ T, path = rest in order, then the other two of T) gives a
  singular matrix for all 6 role assignments (rank 3/4 at N=4, 15-16/20 at
  N=5), and multi-apex families (end b(a)) are not triangular either.
  Fixed apex 0 detectors reach only 3, 9, 45 (N=4,5,6).
* Conclusion: no easy improvement of the constant/shape by this argument;
  (N-2)! is what the clean diagonal gives. The true q_N is far larger, so a
  real improvement needs non-path face functions (leaves, linear/omitted
  states).

## True values of q_N

`rank_grid.py`: evaluate all distinct normalized face functions and A_N at
all primitive integer points of [-R,R]^{N-1} × {x_0 = 0} (translation
invariance reduces to x_0 = 0 exactly), rank mod 2^31 - 1. Each value is a
rigorous lower bound; equality is supported by stability in R.

| N | distinct face descriptions | q_N | (N-2)! | N!/6 |
|---|---|---|---|---|
| 3 | 9 | 1 | 1 | 1 |
| 4 | 138 | 65 (R = 3, 4, 5) | 2 | 4 |
| 5 | 1830 | 1136 (R = 4 and 5) | 6 | 20 |
| 6 | 26780 | >= 6707 (lower bound only: 7000 random grid points, R = 3, mod 524287; not saturated, cf. N = 5 where R = 3 gives 992 < 1136) | 24 | 120 |

q_N grows like the number of face descriptions (ratio 0.47, 0.62 for
N = 4, 5), i.e. roughly N!·3^N up to polynomial factors, much faster than
(N-2)!. N = 7 (~4·10^5 descriptions) was not attempted.

## Lean

`MaxCaterpillar/Simplify/Dimension.lean` (imports only `MaxCaterpillar.Quotient`),
namespace `MaxCaterpillar.Simplify`:

* `factorial_le_quotientDim (r) (hr : 1 ≤ r) : r.factorial ≤ quotientDim r`,
  axioms `[Quot.sound, propext, Classical.choice]`.
* Core lemmas: `Λ` (third mixed difference, a linear map), `Λ_indep`, `Λ_two`
  (kills functions of two coordinates), `feat_two`, `auxSpan_le_ker`,
  `Λ_congr` (only the box matters), `Λ_germ` (= 1), `detector_self`,
  `detector_other`.
* `research/sN/simplify/CheckDimension.lean` derives
  `caterpillarDim_ge_simplified` with type checked `rfl`-equal to
  `caterpillarDim_ge` (via `caterpillarDim_eq`).
* Lines: old `LowerBound.lean` 523 (458 nonblank); new file 402 (347
  nonblank). About 110 lines (path-unit index, `pathUnit_apply`,
  `exists_descent`) are shared infrastructure, copied unchanged.
