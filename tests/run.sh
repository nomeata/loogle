#!/usr/bin/env bash
# End-to-end tests for the loogle binary. Requires that the loogle binary has
# already been built in the parent project's .lake tree (e.g. via `lake build`
# at the repo root).
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
TMP_IDX=$(mktemp -d)/loogle.idx

# Build the test sub-project (MyMod.olean) if not already built.
ensure_built () {
  local proj="$1"
  if [ ! -f "$proj/.lake/build/lib/lean/MyMod.olean" ]; then
    echo "Building $proj..."
    ( cd "$proj" && lake build >/dev/null )
  fi
}

cleanup () {
  rm -f "$TMP_IDX"
  rmdir "$(dirname "$TMP_IDX")" 2>/dev/null || true
  # Restore mutated MyMod.lean
  if [ -f "$TESTS_DIR/lake-env/MyMod.lean.bak" ]; then
    mv "$TESTS_DIR/lake-env/MyMod.lean.bak" "$TESTS_DIR/lake-env/MyMod.lean"
    ( cd "$TESTS_DIR/lake-env" && lake build >/dev/null 2>&1 ) || true
  fi
  # Make sure we don't leave the build dir read-only
  chmod u+w "$TESTS_DIR/lake-env/.lake/build/lib/lean" 2>/dev/null || true
  # Drop any default-location index file we created
  rm -f "$TESTS_DIR/lake-env/.lake/build/lib/lean/MyMod.loogle-index"
  rm -f "$TESTS_DIR/lake-exe/.lake/build/lib/lean/MyMod.loogle-index"
}
trap cleanup EXIT

# Run a command, expect zero exit, diff combined stdout+stderr against $expected.
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

# Run a command, expect zero exit. Diff stdout against $expected_stdout.
# Assert that $stderr_needle appears in stderr (use empty string to skip).
run_scenario_split () {
  local name="$1"
  local expected_stdout="$2"
  local stderr_needle="$3"
  shift 3
  echo "=== Scenario: $name ==="
  echo "+ $*"
  local err_file
  err_file=$(mktemp)
  local out
  if ! out=$("$@" 2>"$err_file"); then
    echo "Command exited non-zero" >&2
    cat "$err_file" >&2
    rm -f "$err_file"
    failures=$((failures + 1))
    return
  fi
  if ! diff -u <(printf '%s\n' "$expected_stdout") <(printf '%s\n' "$out"); then
    echo "Stdout mismatch in scenario $name" >&2
    failures=$((failures + 1))
  fi
  if [ -n "$stderr_needle" ] && ! grep -qF -- "$stderr_needle" "$err_file"; then
    echo "Stderr in scenario $name does not contain '$stderr_needle':" >&2
    cat "$err_file" >&2
    failures=$((failures + 1))
  fi
  # If we expect no stderr noise, complain if there is some.
  if [ -z "$stderr_needle" ] && [ -s "$err_file" ]; then
    echo "Stderr in scenario $name should be empty but contains:" >&2
    cat "$err_file" >&2
    failures=$((failures + 1))
  fi
  rm -f "$err_file"
}

# Run a command, expect non-zero exit and $needle in stderr.
run_scenario_fail () {
  local name="$1"
  local needle="$2"
  shift 2
  echo "=== Scenario: $name (expect failure) ==="
  echo "+ $*"
  local err_file
  err_file=$(mktemp)
  if "$@" >/dev/null 2>"$err_file"; then
    echo "Scenario $name: expected non-zero exit but got 0" >&2
    cat "$err_file" >&2
    rm -f "$err_file"
    failures=$((failures + 1))
    return
  fi
  if ! grep -qF -- "$needle" "$err_file"; then
    echo "Scenario $name: stderr did not contain '$needle':" >&2
    cat "$err_file" >&2
    failures=$((failures + 1))
  fi
  rm -f "$err_file"
}

EXPECTED='Found 2 declarations mentioning myUniqueValue.

myUniqueValue (from MyMod)
myUniqueValue_eq (from MyMod)'

# ---------------------------------------------------------------------------
# Baseline: loogle runs in both `lake exe` and `lake env` invocation patterns.
# ---------------------------------------------------------------------------

ensure_built lake-exe
run_scenario "lake-exe" "$EXPECTED" \
  bash -c "cd $TESTS_DIR/lake-exe && lake exe loogle --module MyMod 'myUniqueValue'"

ensure_built lake-env
run_scenario "lake-env" "$EXPECTED" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --module MyMod 'myUniqueValue'"

# ---------------------------------------------------------------------------
# Index lifecycle scenarios — all in the lake-env project for simplicity.
# ---------------------------------------------------------------------------

DEFAULT_IDX="$TESTS_DIR/lake-env/.lake/build/lib/lean/MyMod.loogle-index"
rm -f "$DEFAULT_IDX" "$TMP_IDX"

# --use-index, first call: builds, writes to default path, warns on stderr.
run_scenario_split "use-index initial build (default path)" \
  "$EXPECTED" "rebuilding" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --use-index --module MyMod 'myUniqueValue'"
[ -f "$DEFAULT_IDX" ] || {
  echo "Expected $DEFAULT_IDX to exist after first --use-index call" >&2
  failures=$((failures + 1))
}

# --use-index, second call: reads the file silently.
run_scenario_split "use-index reuse (default path)" \
  "$EXPECTED" "" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --use-index --module MyMod 'myUniqueValue'"

# --read-index on a fresh index: succeeds silently.
run_scenario_split "read-index on fresh index" \
  "$EXPECTED" "" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --read-index --module MyMod 'myUniqueValue'"

# --index-file override puts the file at a custom path.
rm -f "$TMP_IDX"
run_scenario_split "use-index with --index-file override" \
  "$EXPECTED" "rebuilding" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --use-index --index-file '$TMP_IDX' --module MyMod 'myUniqueValue'"
[ -f "$TMP_IDX" ] || {
  echo "Expected $TMP_IDX to exist after --index-file override" >&2
  failures=$((failures + 1))
}

# --read-index on a missing file: fails non-zero with a helpful message.
run_scenario_fail "read-index on missing file" \
  "no index file at /this/path/does/not/exist.idx" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --read-index --index-file '/this/path/does/not/exist.idx' --module MyMod 'myUniqueValue'"

# Mutate MyMod.lean so the .trace depHash changes; rebuild the olean.
cp "$TESTS_DIR/lake-env/MyMod.lean" "$TESTS_DIR/lake-env/MyMod.lean.bak"
echo "def loogleTestExtraDef : Nat := 1" >> "$TESTS_DIR/lake-env/MyMod.lean"
( cd "$TESTS_DIR/lake-env" && lake build >/dev/null )

# --read-index on the now-stale default index: fails with "is stale".
run_scenario_fail "read-index on stale index" \
  "is stale" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --read-index --module MyMod 'myUniqueValue'"

# --use-index on the same stale index: warns and rebuilds, then succeeds.
run_scenario_split "use-index on stale index (rebuilds)" \
  "$EXPECTED" "is stale" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --use-index --module MyMod 'myUniqueValue'"

# After the rebuild, --read-index should succeed silently again.
run_scenario_split "read-index after use-index rebuilt" \
  "$EXPECTED" "" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --read-index --module MyMod 'myUniqueValue'"

# Restore MyMod.lean (also rebuild) — done via the EXIT trap.

# --write-index against a read-only default location: error message must
# suggest --index-file.
chmod a-w "$TESTS_DIR/lake-env/.lake/build/lib/lean"
run_scenario_fail "write-index to read-only default location" \
  "--index-file" \
  bash -c "cd $TESTS_DIR/lake-env && lake env '$LOOGLE_BIN' --write-index --module MyMod 'myUniqueValue'"
chmod u+w "$TESTS_DIR/lake-env/.lake/build/lib/lean"

# ---------------------------------------------------------------------------
if [ "$failures" -gt 0 ]; then
  echo "FAILED: $failures scenario(s)" >&2
  exit 1
fi
echo "All scenarios passed."
