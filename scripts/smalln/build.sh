#!/usr/bin/env bash
# Build one SmallN instance module by module (`lake build` per module) and
# record wall time, peak memory and exit status of each.  The cell chunks are
# independent and are built JOBS at a time (default 3).
# usage: [JOBS=3] scripts/smalln/build.sh Name [log]
set -u
cd "$(dirname "$0")/../.."
ulimit -s unlimited
name=$1
log=${2:-scripts/smalln/out/build_$name.log}
jobs=${JOBS:-3}
mkdir -p scripts/smalln/out
: > "$log"
one() {
  m=$1; log=$2
  tmp=$(mktemp -d)
  start=$(date +%s.%N)
  /usr/bin/time -f "%M" -o "$tmp/mem" lake build "$m" > "$tmp/out" 2>&1
  st=$?
  end=$(date +%s.%N)
  printf '%s exit=%s wall=%.1fs maxrss=%sKB\n' "$m" "$st" "$(echo "$end - $start" | bc)" \
    "$(tail -1 "$tmp/mem")" | tee -a "$log"
  if [ $st -ne 0 ]; then grep -v '^\[\|✔\|LEAN_PATH' "$tmp/out" | head -40 | tee -a "$log"; fi
  rm -rf "$tmp"
  return $st
}
export -f one
one MaxCaterpillar.SmallN.Common "$log" && one "MaxCaterpillar.SmallN.$name.Defs" "$log" || exit 1
ls MaxCaterpillar/SmallN/$name/ | grep '^Cells' | sed 's/.lean$//' | sort -V |
  xargs -P "$jobs" -I{} bash -c "one MaxCaterpillar.SmallN.$name.{} $log" || exit 1
one "MaxCaterpillar.SmallN.$name" "$log"
