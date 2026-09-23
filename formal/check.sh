#!/usr/bin/env bash
# Run every formal check: the transcription and staleness checks of the Lean
# models, the Lean proofs, and the TLA+ models.
#
#   formal/check.sh            # everything
#   formal/check.sh lean       # only the Lean side
#   formal/check.sh tla        # only TLC
#
# Needs: python3; Lean 4.34 via elan (lake); for TLC a Java runtime and
# tla2tools.jar (set JAVA and TLA2TOOLS, see formal/tla/README.md).
set -euo pipefail
cd "$(dirname "$0")/.."
what=${1:-all}

if [[ "$what" == all || "$what" == lean ]]; then
  echo "== transcriptions and generated Lean files"
  python3 formal/tools/check_transcriptions.py
  python3 formal/tools/kernels_to_lean.py --check
  python3 formal/tools/keccak_to_lean.py --check
  echo "== Lean"
  (cd formal/lean && lake build)
  if grep -rn --include='*.lean' -E '\bsorry\b|native_decide|^\s*axiom ' formal/lean/Curve448Formal \
       | grep -v -E '^\S+:\s*[0-9]+:\s*(--|Main results|The|/-)' | grep -v 'no `sorry`'; then
    echo "found sorry / native_decide / axiom in the Lean sources" >&2
    exit 1
  fi
fi

if [[ "$what" == all || "$what" == tla ]]; then
  echo "== TLA+"
  formal/tla/check.sh
fi
