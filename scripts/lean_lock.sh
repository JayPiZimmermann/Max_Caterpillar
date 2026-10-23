#!/usr/bin/env bash
# Run a Lean command under a machine-wide lock, so at most one Lean build or
# `lake env lean` check runs at a time (each can peak near 5 GB of RAM).
# Usage: scripts/lean_lock.sh lake build MaxCaterpillar.Foo
#        scripts/lean_lock.sh lake env lean path/File.lean
ulimit -s unlimited
exec flock /tmp/max_caterpillar_lean.lock "$@"
