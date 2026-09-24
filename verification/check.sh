#!/bin/sh
# Re-run every Lean proof and TLA+ model check in this directory.
#   TLA2TOOLS  path to tla2tools.jar (default: ~/.local/share/tlaplus/tla2tools.jar)
#   JAVA       java executable (default: Homebrew OpenJDK, see tla/run_all.sh)
set -eu
here=$(cd "$(dirname "$0")" && pwd)

echo "== Lean: building proofs"
(cd "$here/lean" && lake build)

echo "== Lean: axiom audit"
axioms=$(cd "$here/lean" && lake env lean scripts/Axioms.lean)
echo "$axioms"
if echo "$axioms" | grep -Eq 'sorryAx|ofReduceBool|trustCompiler'; then
  echo "FAIL: a theorem depends on sorry or native evaluation" >&2
  exit 1
fi

echo "== TLA+: model checking (see tla/README.md)"
"$here/tla/run_all.sh"

echo "== all checks passed"
