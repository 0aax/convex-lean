#!/usr/bin/env bash
# Grader for the autoformalization task. The reward only records whether the
# submission has the required shape (builds; one theorem `BC_chap_9_20` whose
# proof is `sorry`; no other sorry; no axiom/opaque; pinned files intact). The
# statement itself is assessed by people from the artifacts, so the statement
# file is also copied to /logs/verifier/statement.lean for convenience.
set -u
PKG=/app/autoformalize
FILE=LeanWorkspace/BC_chap_9_20.lean
NAME=BC_chap_9_20
cd "$PKG"
mkdir -p /logs/verifier
: > /logs/verifier/checks.log

for f in lakefile.toml lean-toolchain lake-manifest.json LeanWorkspace.lean; do
  if ! cmp -s "/opt/pristine/$f" "$f"; then
    echo "WARN: $f was modified; pristine copy restored for grading" >> /logs/verifier/checks.log
    cp -f "/opt/pristine/$f" "$f"
  fi
done

# Stop anything the agent left running so the build is not contended.
STRAY=$( (pgrep -a -x python3; pgrep -a -x python3.12; pgrep -a -x python; pgrep -a -x lean; pgrep -a -x lake; pgrep -a -x sleep; pgrep -a -x node) 2>/dev/null | grep -vE 'daytona_repl_worker|sleep infinity' || true)
if [ -n "$STRAY" ]; then
  echo "NOTE: stopped stray agent processes before grading:" >> /logs/verifier/checks.log
  echo "$STRAY" | sed 's/^/      /' >> /logs/verifier/checks.log
  echo "$STRAY" | awk '{print $1}' | xargs -r kill 2>/dev/null
  sleep 2
  echo "$STRAY" | awk '{print $1}' | xargs -r kill -9 2>/dev/null
fi

OK=1
if [ -f "$FILE" ]; then
  cp -f "$FILE" /logs/verifier/statement.lean
else
  echo "FAIL: $FILE is missing" >> /logs/verifier/checks.log
  OK=0
fi

cp -f "LeanWorkspace/FCA_chap_B_1_2_1.lean" /logs/verifier/prior.lean 2>/dev/null || echo "NOTE: LeanWorkspace/FCA_chap_B_1_2_1.lean was removed" >> /logs/verifier/checks.log
cp -f LeanWorkspace/Defs.lean /logs/verifier/defs.lean 2>/dev/null || echo "NOTE: LeanWorkspace/Defs.lean was removed" >> /logs/verifier/checks.log

rm -rf .lake/build
if lake build LeanWorkspace > /logs/verifier/lake_build.log 2>&1; then
  echo "lake build LeanWorkspace succeeded" >> /logs/verifier/checks.log
else
  echo "FAIL: lake build LeanWorkspace failed" >> /logs/verifier/checks.log
  tail -n 25 /logs/verifier/lake_build.log >> /logs/verifier/checks.log
  OK=0
fi

if [ -f "$FILE" ]; then
  if python3 /opt/pristine/check_statement.py "$FILE" "$NAME" > /logs/verifier/format.log 2>&1; then
    echo "format check passed" >> /logs/verifier/checks.log
  else
    echo "FAIL: format check:" >> /logs/verifier/checks.log
    sed 's/^/  - /' /logs/verifier/format.log >> /logs/verifier/checks.log
    OK=0
  fi
fi

if [ -f LeanWorkspace/Defs.lean ]; then
  DEFS_ISSUES=$(python3 -c 'import re, sys; sys.path.insert(0, "/opt/pristine"); import check_statement as c; t = c.strip_comments(open(sys.argv[1]).read()); [print(k) for k in ("sorry", "axiom", "opaque") if re.search(rf"\b{k}\b", t)]' LeanWorkspace/Defs.lean)
  if [ -n "$DEFS_ISSUES" ]; then
    echo "FAIL: LeanWorkspace/Defs.lean uses: $DEFS_ISSUES" >> /logs/verifier/checks.log
    OK=0
  fi
fi

echo "$OK" > /logs/verifier/reward.txt

# The sandbox is discarded after this script, and Harbor collects /app as the
# trial's artifacts. Remove the Lake build tree and the vendored Mathlib sources
# (~700 MB, thousands of .lean files) so they can never end up in the artifacts;
# the tar exclude patterns in task.toml have let `.lake/packages` through when the
# agent recreated `.lake` during the run.
rm -rf "$PKG/.lake"
# Harbor extracts the artifact tarball with Python's `data` filter, which aborts the
# whole extraction on a symlink to an absolute path (e.g. `bin/python3` inside a
# virtualenv an agent created under /app/scratch). Symlinks are never needed in the
# artifacts, so drop them all before collection.
find /app -xdev -type l -delete 2>/dev/null || true
