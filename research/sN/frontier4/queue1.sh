#!/bin/bash
# MEASURED scan: free-first-layer fits for max_4, sequential, 300 s each.
PY=/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-general-neurons/venv/bin/python
cd /home/jzimmermann/code/Max_Caterpillar/research/sN/frontier4
for c in "6 3" "5 3" "5 4" "6 2" "8 2" "5 5" "4 4"; do
  set -- $c
  OMP_NUM_THREADS=4 timeout 400 $PY fit.py free 4 $1 $2 400 1 2000 300 > logs/fit_h$1_$2_s1.log 2>&1
done
