#!/usr/bin/env bash
# Fail if `lake build` emits a warning in a SteppedFlapjack module outside
# SteppedFlapjack/Test/. Adapted from Flapjack's scripts/check-warnings.sh.
#
# Run this after lean-action has already built: Lake replays diagnostics from
# its cache, so this second build is close to free and still reports every
# warning, not just the modules that happened to rebuild. Warnings from the
# Flapjack dependency are not counted.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1

log=$(mktemp)
trap 'rm -f "$log"' EXIT

lake build >"$log" 2>&1
build_status=$?

if [ "$build_status" -ne 0 ]; then
  echo "error: lake build failed" >&2
  grep -E '^error' "$log" >&2 | head -50
  exit "$build_status"
fi

is_ours='/^warning: SteppedFlapjack(\.lean|\/)/ && !/^warning: SteppedFlapjack\/Test\//'
count=$(awk "$is_ours { n++ } END { print n+0 }" "$log")

if [ "$count" -ne 0 ]; then
  echo "FAIL: lake build emitted $count non-test warning(s)" >&2
  echo >&2
  awk "/^warning:/ { remaining = 0 } $is_ours { remaining = 4 }
       remaining > 0 { print; remaining-- }" "$log" >&2 | head -120
  cat >&2 <<'MSG'

The build is expected to be warning-free outside SteppedFlapjack/Test/. Lean's
linters print the exact correction for most of these; apply that rather than
silencing the warning with `set_option linter.… false`.
MSG
  exit 1
fi

echo "lake build: 0 non-test warnings"
