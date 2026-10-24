#!/bin/bash
# Sequential queue of fits (one heavy computation at a time). Each line of the queue file:
#   <script> <args...>      run with the venv python, log to logs/<script>_<args>.log
PY=/home/jzimmermann/code/Max_Caterpillar/research/sN/dfs/h4-general-neurons/venv/bin/python
cd /home/jzimmermann/code/Max_Caterpillar/research/sN/best5
while read -r line; do
  [ -z "$line" ] && continue
  case "$line" in \#*) continue;; esac
  name=$(echo "$line" | tr ' ' '_' | sed 's/\.py//')
  echo "$(date +%T) start $line" >> logs/queue.log
  OMP_NUM_THREADS=2 timeout 5400 $PY $line > logs/$name.log 2>&1
  echo "$(date +%T) end $line exit $?" >> logs/queue.log
done < "$1"
