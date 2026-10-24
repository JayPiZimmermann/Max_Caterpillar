#!/bin/bash
# symmetric ansatz runs for N=6 (subgroups of S_6); logs in logs/sym6_<tag>.log
cd "$(dirname "$0")"
declare -A G
G[S5]="0,2,1,3,4,5;0,2,3,4,5,1"
G[S3xS3]="1,0,2,3,4,5;1,2,0,3,4,5;0,1,2,4,3,5;0,1,2,4,5,3"
G[S4xS2]="1,0,2,3,4,5;1,2,3,0,4,5;0,1,2,3,5,4"
G[D6]="1,2,3,4,5,0;5,4,3,2,1,0"
G[S2wrS3]="1,0,2,3,4,5;2,3,0,1,4,5;2,3,4,5,0,1"
G[S3wrS2]="1,0,2,3,4,5;1,2,0,3,4,5;3,4,5,0,1,2"
for t in "${!G[@]}"; do
  timeout 3000 ../h5-growth/venv/bin/python symsolve.py 6 full "${G[$t]}" 1 data/sym6_$t.pkl > logs/sym6_$t.log 2>&1
done
