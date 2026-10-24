#!/bin/bash
cd "$(dirname "$0")"
for m in 5 6 7 8 9 10; do
  timeout 7000 ./venv/bin/python dfs.py 5 $m full > logs/dfs_5_full_$m.log 2>&1
  echo EXIT=$? >> logs/dfs_5_full_$m.log
  grep -q SOLUTION logs/dfs_5_full_$m.log && break
done
