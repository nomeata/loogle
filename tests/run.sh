#!/usr/bin/env bash
# End-to-end tests for the loogle binary in both "lake env" and "lake exe"
# usage patterns. Requires that the loogle binary has already been built
# in the parent project's .lake tree (e.g. via `lake build` at the repo root).
set -euo pipefail

cd "$(dirname "$0")"
TESTS_DIR=$(pwd)
ROOT=$(cd .. && pwd)
LOOGLE_BIN="$ROOT/.lake/build/bin/loogle"

if [ ! -x "$LOOGLE_BIN" ]; then
  echo "loogle binary not found at $LOOGLE_BIN" >&2
  echo "Build it first: lake build" >&2
  exit 1
fi

failures=0

# Build the test sub-project (MyMod.olean) if not already built.
ensure_built () {
  local proj="$1"
  if [ ! -f "$proj/.lake/build/lib/lean/MyMod.olean" ]; then
    echo "Building $proj..."
    ( cd "$proj" && lake build >/dev/null )
  fi
}

run_scenario () {
  local name="$1"
  local expected="$2"
  shift 2
  echo "=== Scenario: $name ==="
  echo "+ $*"
  local actual
  if ! actual=$("$@" 2>&1); then
    echo "Command exited non-zero" >&2
    echo "$actual" >&2
    failures=$((failures + 1))
    return
  fi
  if ! diff -u <(printf '%s\n' "$expected") <(printf '%s\n' "$actual"); then
    echo "Output mismatch in scenario $name" >&2
    failures=$((failures + 1))
  fi
}

EXPECTED='Found 2 declarations mentioning myUniqueValue.

myUniqueValue (from MyMod)
myUniqueValue_eq (from MyMod)'

# Scenario A: lake exe pattern — loogle declared as a lake require, run via
# `lake exe loogle` so it's built and invoked through the dep graph.
ensure_built lake-exe
run_scenario "lake-exe" "$EXPECTED" \
  bash -c "cd $TESTS_DIR/lake-exe && lake exe loogle --module MyMod 'myUniqueValue'"

# Scenario B: lake env pattern — loogle NOT a lake dep; invoke the binary
# explicitly via the project's `lake env` so LEAN_PATH points at MyMod.
ensure_built lake-env
run_scenario "lake-env" "$EXPECTED" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --module MyMod 'myUniqueValue'"

if [ "$failures" -gt 0 ]; then
  echo "FAILED: $failures scenario(s)" >&2
  exit 1
fi
echo "All scenarios passed."
