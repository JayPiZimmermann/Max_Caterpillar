#!/bin/bash
# kill python processes whose cmdline contains $1 (never shells)
for p in $(pgrep -f "$1"); do
  c=$(tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null)
  case "$c" in *python*) [[ "$c" != *bash* ]] && kill $p && echo killed $p;; esac
done
