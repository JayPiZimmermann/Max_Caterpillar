# dimension (simplify q_N >= (N-2)!) -- progress log

- Step 0: read Definitions/Theorems/LowerBound/Quotient and paper app:quotient-lower.
  Existing Lean proof: LowerBound.lean (~480 lines of proof), diagonal argument
  with path units, second difference in x_0, test minus reference configuration.
- Step 1: computed q_N (rank_grid.py, exact integer eval at primitive grid points,
  rank mod 2^31-1; lower bound always valid, stability = evidence):
  q_3 = 1, q_4 = 65 (stable R=3..5), q_5 = 1136 (R=4; R=5 run in grid_5_5.log).
  Distinct normalized descriptions: 9, 138, 1830, 26780 (N=3..6).
  Path units (all-hinge paths): apex 0 & end fixed: rank (N-2)! (2, 6);
  apex 0 any end: 3/3 distinct (N=4), 11/12 (N=5) (path = reversed path);
  all apexes: 12/12, 55/60. So paths alone cannot give N!/2 at N=5.
- Step 2: NEW simpler functional found: third mixed difference in x_0, x_b, x_c
  (c = last middle label of rho) at z with z_0 = z_b = z_c = N-2, z_{rho(j)} = j.
  Kills A because every auxiliary function misses one of the three coordinates;
  no reference configuration needed. Diagonal = -s, off-diagonal 0 via descent.
- Step 5: Lean file MaxCaterpillar/Simplify/Dimension.lean written; check_diag.py confirms identity matrix N=3..7; dimension.md drafted.
- Step 6: MaxCaterpillar/Simplify/Dimension.lean compiles (lake build OK);
  MaxCaterpillar.Simplify.factorial_le_quotientDim : r.factorial ≤ quotientDim r,
  axioms [Quot.sound, propext, Classical.choice]. CheckDimension.lean (research dir)
  proves caterpillarDim_ge_simplified with type defeq-checked against caterpillarDim_ge.
  Lines: old LowerBound.lean 523 (458 nonblank), new 402 (347 nonblank).
- Step 7: q_6 >= 6707 (lower bound, q6_lower.log). dimension.md finalized.
