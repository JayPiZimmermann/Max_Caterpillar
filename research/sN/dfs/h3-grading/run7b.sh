#!/bin/bash
# N=7 multiplicities m_lam(V_7) by grade via Young symmetrizers (ysym2.py), npts = 130 f_lam + 400.
# Mod-p ranks of random evaluations: lower bounds (measured).  3 jobs in parallel, 90 min cap each.
V=/tmp/claude-1342076897/-home-jzimmermann-code-Max-Caterpillar/959f7190-775e-44f9-8707-e5e072ae6f20/scratchpad/venv/bin/python
cd "$(dirname "$0")"
printf '%s\n' "7 530" "1111111 530" "61 1180" "211111 1180" "52 2220" "22111 2220" "511 2350" "31111 2350" "43 2220" "2221 2220" "421 4950" "3211 4950" "4111 3000" "331 3130" "322 3130" | \
  xargs -P 3 -L 1 sh -c 'OMP_NUM_THREADS=1 timeout 5400 nice '"$V"' ysym2.py 7 $0 $1 >> ysym3_7.log 2>> ysym3_7.err'
echo done >> ysym3_7.err
