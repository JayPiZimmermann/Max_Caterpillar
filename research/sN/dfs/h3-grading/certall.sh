#!/bin/bash
# usage: certall.sh N jobs mu1:tw1 mu2:tw2 ... ; appends to cert_N.log
N=$1; J=$2; shift 2
V=/tmp/claude-1342076897/-home-jzimmermann-code-Max-Caterpillar/959f7190-775e-44f9-8707-e5e072ae6f20/scratchpad/venv/bin/python
for a in "$@"; do echo ${a%%:*} ${a##*:}; done | xargs -P $J -n 2 sh -c "$V certify.py $N \$0 \$1 40 3" >> cert_$N.log 2>> cert_$N.err
