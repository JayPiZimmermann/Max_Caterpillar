#!/bin/bash
# N=7 multiplicities; npts = 80 f_lam + 150 (rerun with more if saturated)
V=/tmp/claude-1342076897/-home-jzimmermann-code-Max-Caterpillar/959f7190-775e-44f9-8707-e5e072ae6f20/scratchpad/venv/bin/python
for a in "7 230" "1111111 230" "61 630" "211111 630" "52 1270" "22111 1270" "511 1350" "31111 1350" "43 1270" "2221 1270" "421 2950" "3211 2950" "4111 1750" "331 1830" "322 1830"; do
  set -- $a
  OMP_NUM_THREADS=6 $V ysym2.py 7 $1 $2 >> ysym2_7.log 2>> ysym2_7.err
done
