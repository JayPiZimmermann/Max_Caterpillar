#!/bin/bash
# N=7 Young-subgroup (twisted) fixed-space ranks via young7.py, for the multiplicities of
# 421, 3211, 4111, 331, 322 (Kostka inversion against ysym3_7.log).  2 jobs in parallel, 90 min cap.
V=/tmp/claude-1342076897/-home-jzimmermann-code-Max-Caterpillar/959f7190-775e-44f9-8707-e5e072ae6f20/scratchpad/venv/bin/python
cd "$(dirname "$0")"
printf '%s\n' "331 sgn" "331 triv" "421 sgn" "4111 sgn" "421 triv" | \
  xargs -P 2 -L 1 sh -c 'OMP_NUM_THREADS=2 timeout 5400 '"$V"' young7.py 7 $0 $1 >> young7_7.log 2>> young7_7.err'
echo done >> young7_7.err
