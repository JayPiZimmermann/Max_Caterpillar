#!/usr/bin/env bash
# Local Lean compilation and exact-type/axiom checks. No GitHub operations.
set -euo pipefail
proof_repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$proof_repo_root"
proof_dir=research/sN/width_tradeoff
mkdir -p "$proof_dir/verification"

proof_modules=(
  "$proof_dir/Frontier"
  "$proof_dir/AuditTent"
  "$proof_dir/LowerFirst"
  "$proof_dir/LowerTransverse"
  "$proof_dir/UpperMax5"
  research/sN/frontierN/overnight_general_antipodal
  "$proof_dir/UpperNineDefs"
  "$proof_dir/UpperNineCells0"
  "$proof_dir/UpperNineCells1"
  "$proof_dir/UpperNineCells2"
  "$proof_dir/UpperNineCells3"
  "$proof_dir/UpperNineIdentity"
  "$proof_dir/UpperNineNetwork"
  "$proof_dir/Checks"
)

for proof_module in "${proof_modules[@]}"; do
  proof_log="$proof_dir/verification/${proof_module##*/}.log"
  printf 'Checking %s\n' "$proof_module"
  if lake env bash -c '
    export LEAN_PATH="$LEAN_PATH:."
    lean -j1 -o "$1.olean" "$1.lean"
  ' _ "$proof_module" > "$proof_log" 2>&1; then
    printf 'EXIT_CODE=0\n' >> "$proof_log"
  else
    proof_status=$?
    printf 'EXIT_CODE=%s\n' "$proof_status" >> "$proof_log"
    tail -n 40 "$proof_log"
    exit "$proof_status"
  fi
done

# This checks the printed audit output; it does not perform mathematical search.
python3 - <<'PY'
from pathlib import Path
import re

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
reports = 0
for path in sorted(Path('research/sN/width_tradeoff/verification').glob('*.log')):
    text = path.read_text()
    if not text.endswith('EXIT_CODE=0\n'):
        raise SystemExit(f'Missing successful completion: {path}')
    for block in re.findall(r'depends on axioms:\s*\[([^]]*)\]', text):
        axioms = {name.strip() for name in block.split(',') if name.strip()}
        if not axioms <= allowed:
            raise SystemExit(f'Unpermitted axioms in {path}: {axioms - allowed}')
        reports += 1
if reports < 15:
    raise SystemExit(f'Unexpectedly few axiom audits: {reports}')
print(f'PASS: {reports} axiom audits, only the three permitted standard axioms.')
PY

proof_sources=()
for proof_module in "${proof_modules[@]}"; do
  proof_sources+=("$proof_module.lean")
done
sha256sum "${proof_sources[@]}" "$proof_dir/verify.sh" \
  > "$proof_dir/verification/SOURCES.sha256"
