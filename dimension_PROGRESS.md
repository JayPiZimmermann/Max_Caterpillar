- Step 3: q_5 = 1136 confirmed (R=4 and R=5 grids agree). Detector rank checks:
  3-coordinate detectors on all path units have rank exactly N!/6 (N=4,5,6:
  4, 20, 120); apex-0 only: 3, 9, 45. Uniform "monotone unit" selections for
  N!/6 are singular (tri.py, tri2.py); multi-apex families not triangular
  (multi_apex.py). No easy clean improvement beyond (N-2)! found.
- Step 4: q_6 lower bound running (big_rank.py, 7000 points) -> q6_lower.log.
- Policy (coordinator): new proof REPLACES old; report unused old declarations.
