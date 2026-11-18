#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

mode=${1:-}
if [[ $# -gt 1 || ( -n "$mode" && "$mode" != --audit-only && "$mode" != --two-jobs ) ]]; then
  printf 'Usage: %s [--audit-only | --two-jobs]\n' "$0" >&2
  exit 2
fi

lean --version
lake --version
cat lean-toolchain
printf 'Mathlib revision: '
git -C .lake/packages/mathlib rev-parse HEAD
if rg -n '^\s*(private )?(unsafe|axiom)\b|\b(native_decide|sorryAx)\b|(^|\s)(sorry|admit)(\s|$)'     NilBohr.lean NilBohr/; then
  printf 'Found a forbidden declaration or proof placeholder.\n' >&2
  exit 1
fi
if [[ $mode != --audit-only ]]; then
  printf 'Clearing the project build directory only: .lake/build\n'
  rm -rf -- .lake/build
  if [[ $mode == --two-jobs ]]; then
    printf 'Running python3 scripts/build_two_jobs.py\n'
    LEAN_NUM_THREADS=2 python3 scripts/build_two_jobs.py
  else
    printf 'Running lake build\n'
    lake build
  fi
fi
printf 'Running lake env lean scripts/CheckAxioms.lean\n'
audit_log=$(mktemp)
trap 'rm -f -- "$audit_log"' EXIT
lake env lean scripts/CheckAxioms.lean | tee "$audit_log"
python3 - "$audit_log" <<'PY'
import re
import sys
from pathlib import Path

expected = set(re.findall(r"^#print axioms (\S+)", Path("scripts/CheckAxioms.lean").read_text(), re.M))
output = Path(sys.argv[1]).read_text()
found = set()
used = set()
for name, tail in re.findall(r"^'([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)", output, re.M):
    found.add(name)
    if "[" in tail:
        used.update(axiom.strip() for axiom in tail.split("[", 1)[1][:-1].split(","))
unexpected = used - {"propext", "Classical.choice", "Quot.sound"}
if expected != found or unexpected:
    raise SystemExit(f"Axiom audit mismatch. Missing {expected - found}, extra {found - expected}, unexpected axioms {unexpected}")
print(f"Axiom audit passed for {len(found)} public theorems. Axioms: {', '.join(sorted(used))}")
PY
(
  cd manuscript
  sha256sum -c SHA256SUMS
)
