#!/usr/bin/env bash
# Parse every module with SANY and model-check every configuration with TLC.
# Models under mutants/ contain deliberate bugs and are expected to FAIL,
# except mutants/Ladder_nofinal_clamped.cfg, which is expected to PASS (see
# the file).  TLC metadata goes to a temporary directory, not the repo.
#
#   JAVA=/opt/homebrew/opt/openjdk/bin/java \
#   TLA2TOOLS=$HOME/.local/share/tlaplus/tla2tools.jar ./check.sh [filter]
set -u
cd "$(dirname "$0")"
JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
TLA2TOOLS=${TLA2TOOLS:-$HOME/.local/share/tlaplus/tla2tools.jar}
META=${META:-$(mktemp -d "${TMPDIR:-/tmp}/tlc-meta.XXXXXX")}
FILTER=${1:-}
status=0

for m in Sponge LadderStep Ladder ScalarMultSchedule; do
  if ! "$JAVA" -cp "$TLA2TOOLS" tla2sany.SANY "$m.tla" > "$META/sany-$m.txt" 2>&1 \
     || grep -q -i "error" "$META/sany-$m.txt"; then
    echo "SANY $m: FAILED"; cat "$META/sany-$m.txt"; status=1
  else
    echo "SANY $m: ok"
  fi
done

# config  module  expected
runs=(
  "Sponge_ocaml.cfg Sponge pass"
  "Sponge_c.cfg Sponge pass"
  "Sponge_digest_ocaml.cfg Sponge pass"
  "Sponge_digest_c.cfg Sponge pass"
  "Sponge_ed448_ocaml.cfg Sponge pass"
  "Sponge_ed448_c.cfg Sponge pass"
  "LadderStep.cfg LadderStep pass"
  "Ladder.cfg Ladder pass"
  "Ladder_unclamped.cfg Ladder pass"
  "Ladder_unclamped_composite.cfg Ladder pass"
  "Ladder_wide.cfg Ladder pass"
  "Ladder_bytes8.cfg Ladder pass"
  "ScalarMultSchedule_symbolic.cfg ScalarMultSchedule pass"
  "ScalarMultSchedule_concrete_npl2.cfg ScalarMultSchedule pass"
  "ScalarMultSchedule_concrete_npl3.cfg ScalarMultSchedule pass"
  "mutants/Sponge_fast_no_pos.cfg Sponge fail"
  "mutants/Sponge_fast_read_off.cfg Sponge fail"
  "mutants/Sponge_pad_at_rate.cfg Sponge fail"
  "mutants/Sponge_squeeze_early_perm.cfg Sponge fail"
  "mutants/Sponge_c_no_reset.cfg Sponge fail"
  "mutants/LadderStep_c_swap_71_74.cfg LadderStep fail"
  "mutants/LadderStep_c_77_reads_bb.cfg LadderStep fail"
  "mutants/LadderStep_ml_drop_55.cfg LadderStep fail"
  "mutants/Ladder_noxor.cfg Ladder fail"
  "mutants/Ladder_nofinal.cfg Ladder fail"
  "mutants/Ladder_nofinal_clamped.cfg Ladder pass"
  "mutants/Ladder_xonly.cfg Ladder fail"
  "mutants/ScalarMultSchedule_unbounded.cfg ScalarMultSchedule fail"
)

for r in "${runs[@]}"; do
  set -- $r
  cfg=$1 mod=$2 expect=$3
  [[ -n "$FILTER" && "$cfg" != *"$FILTER"* ]] && continue
  name=$(echo "$cfg" | tr '/.' '__')
  out="$META/$name.out"
  "$JAVA" -XX:+UseParallelGC -cp "$TLA2TOOLS" tlc2.TLC -workers auto -deadlock \
    -metadir "$META/$name" -config "$cfg" "$mod.tla" > "$out" 2>&1
  if grep -q "No error has been found" "$out"; then got=pass
  elif grep -q "^Error: Invariant .* is violated" "$out"; then got=fail
  else got=error; fi
  stats=$(grep -E "states generated" "$out" | tail -1 | sed -E \
    's/([0-9]+) states generated, ([0-9]+) distinct states found, ([0-9]+) states left on queue./\1 generated, \2 distinct, \3 queued/')
  depth=$(grep -E "depth of the complete state graph" "$out" | sed 's/.* is \([0-9]*\).*/\1/')
  secs=$(grep -E "^Finished in" "$out" | sed 's/Finished in \([^ ]*\) .*/\1/')
  viol=$(grep -E "^Error: Invariant .* is violated" "$out" | sed 's/Error: //')
  verdict=OK; [[ "$got" != "$expect" ]] && { verdict=UNEXPECTED; status=1; }
  printf '%-48s %-5s %-10s %s; depth %s; %s %s\n' "$cfg" "$got" "$verdict" \
    "$stats" "${depth:-?}" "${secs:-?}" "$viol"
  [[ "$got" == error ]] && tail -20 "$out"
done
echo "TLC output in $META"
exit $status
