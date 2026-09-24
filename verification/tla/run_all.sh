#!/bin/sh
# Model-check every configuration and store the TLC output in results/.
#
#   JAVA=... TLA2TOOLS=... ./run_all.sh [cfg-name-substring]
#
# Each configuration states its expected outcome ("pass" or the name of the
# property TLC must report as violated); the script compares it with TLC's
# verdict.  TLC metadata (states/) goes to a temporary directory.  For a
# ParallelRadixSort counterexample, results/<cfg>.trace.txt is a one-line-
# per-state summary of the trace (see trace_summary.py).
set -u
cd "$(dirname "$0")"

JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
TLA2TOOLS=${TLA2TOOLS:-$HOME/.local/share/tlaplus/tla2tools.jar}
if [ -n "${TLC_METADIR:-}" ]; then
  META=$TLC_METADIR
else
  META=$(mktemp -d "${TMPDIR:-/tmp}/tlc-radix.XXXXXX")
  trap 'rm -rf "$META"' EXIT
fi
FILTER=${1:-}

mkdir -p results

# cfg                                              spec                expected
RUNS='
ChooseWorkersChunk_scaled                          ChooseWorkersChunk  pass
ChooseWorkersChunk_real                            ChooseWorkersChunk  pass
AmericanFlagSort_radix                             AmericanFlagSort    pass
AmericanFlagSort_radix_deep                        AmericanFlagSort    pass
AmericanFlagSort_mixed                             AmericanFlagSort    pass
AmericanFlagSort_mixed3                            AmericanFlagSort    pass
AmericanFlagSort_slices                            AmericanFlagSort    pass
AmericanFlagSort_slices_mixed                      AmericanFlagSort    pass
ParallelRadixSort_original_nofail                  ParallelRadixSort   pass
ParallelRadixSort_original_nofail_w2               ParallelRadixSort   pass
ParallelRadixSort_original_nofail_n5               ParallelRadixSort   pass
ParallelRadixSort_original_spawnfail              ParallelRadixSort   QuiescentOnReturn
ParallelRadixSort_original_spawnfail_contents     ParallelRadixSort   ContentsPreservedOnException
ParallelRadixSort_original_spawnfail_mutation     ParallelRadixSort   NoMutationAfterReturn
ParallelRadixSort_original_callerraise            ParallelRadixSort   QuiescentOnReturn
ParallelRadixSort_original_callerraise_contents   ParallelRadixSort   ContentsPreservedOnException
ParallelRadixSort_fixed                            ParallelRadixSort   pass
ParallelRadixSort_fixed_w4                         ParallelRadixSort   pass
ParallelRadixSort_fixed_callerraise                ParallelRadixSort   pass
ParallelRadixSort_fixed_callerraise_contents      ParallelRadixSort   ContentsPreservedOnException
ParallelRadixSort_sequential_callerraise_contents ParallelRadixSort   ContentsPreservedOnException
'

status=0
while read -r cfg spec expected; do
  [ -z "$cfg" ] && continue
  case "$cfg" in *"$FILTER"*) ;; *) continue ;; esac
  out="results/$cfg.out"
  start=$(date +%s)
  # Expected-violation runs are tiny: one worker gives a deterministic trace.
  if [ "$expected" = pass ]; then workers=auto; else workers=1; fi
  "$JAVA" -XX:+UseParallelGC -cp "$TLA2TOOLS" tlc2.TLC -workers "$workers" \
      -difftrace -metadir "$META/$cfg" -config "$cfg.cfg" "$spec.tla" 2>&1 \
    | grep -v -e '^Parsing file' -e '^Semantic processing' > "$out"
  secs=$(( $(date +%s) - start ))
  states=$(grep -o '[0-9 ]* distinct states found' "$out" | tail -1 | tr -d ' ' | sed 's/distinctstatesfound//')
  if grep -q '^Model checking completed. No error has been found.' "$out"; then
    verdict=pass
  else
    verdict=$(grep -o -E '(Invariant|Action property|Temporal properties|property) [A-Za-z]* (is|was) violated' "$out" \
              | head -1 | awk '{print $(NF-2)}')
    [ -z "$verdict" ] && verdict="ERROR(see $out)"
  fi
  if [ "$verdict" = "$expected" ]; then ok=OK; else ok=UNEXPECTED; status=1; fi
  if [ "$verdict" != pass ] && [ "$spec" = ParallelRadixSort ]; then
    python3 trace_summary.py "$out" > "results/$cfg.trace.txt"
  fi
  printf '%-50s %-30s %10s states %5ss  %s\n' "$cfg" "$verdict" "$states" "$secs" "$ok"
done <<EOF
$RUNS
EOF
exit $status
