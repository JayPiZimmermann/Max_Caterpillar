#!/bin/bash
# usage: runall.sh N maxjobs ; writes grade_N.log (JSON lines)
N=$1; J=${2:-4}
V=/tmp/claude-1342076897/-home-jzimmermann-code-Max-Caterpillar/959f7190-775e-44f9-8707-e5e072ae6f20/scratchpad/venv/bin/python
MUS=$($V -c "from kostka import partitions; print(' '.join(''.join(map(str,p)) for p in partitions($N)))")
for mu in $MUS; do for tw in triv sgn; do echo "$mu $tw"; done; done | \
  xargs -P $J -n 2 sh -c "$V grade.py $N \$0 \$1 40 1" >> grade_$N.log
