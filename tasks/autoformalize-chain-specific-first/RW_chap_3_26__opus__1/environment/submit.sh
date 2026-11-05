#!/usr/bin/env bash
# `submit`: in-run format check for the autoformalization task. It runs the same
# checks as the grader (tests/test.sh) on LeanWorkspace/RW_chap_3_26.lean as it is on
# disk and reports the result, with reasons when it fails. It does not end the
# run; the statement is assessed by people afterwards.
set -u
PKG=/app/autoformalize
FILE=LeanWorkspace/RW_chap_3_26.lean
NAME=RW_chap_3_26
LOGDIR=/logs/agent/submit

if [ $# -ne 0 ]; then
  cat <<'USAGE'
usage: submit
  check the format of your statement in LeanWorkspace/RW_chap_3_26.lean:
  it must build, declare a theorem `RW_chap_3_26` whose proof is `sorry`,
  contain no other `sorry` and no `axiom`/`opaque`, and leave the pinned
  files unchanged. The build can take a minute; run it with a generous timeout.
USAGE
  exit 2
fi

mkdir -p "$LOGDIR"
cd "$PKG" || { echo "REJECTED: $PKG is missing"; exit 0; }
N=$(printf '%03d' $(( $(ls "$LOGDIR" 2>/dev/null | grep -c -- '\.log$') + 1 )))
LOG=$LOGDIR/$N.log
: > "$LOG"
FAIL=0

for f in lakefile.toml lean-toolchain lake-manifest.json LeanWorkspace.lean; do
  if ! cmp -s "/opt/pristine/$f" "$f"; then
    echo "pinned file $f was modified; pristine copy restored" | tee -a "$LOG"
    cp -f "/opt/pristine/$f" "$f"
  fi
done

if [ ! -f "$FILE" ]; then
  echo "REJECTED: $FILE does not exist" | tee -a "$LOG"
  exit 0
fi

if ! lake build LeanWorkspace >> "$LOG" 2>&1; then
  echo "REJECTED: lake build LeanWorkspace failed; last lines of the build log:"
  tail -n 25 "$LOG" | sed 's/^/  /'
  FAIL=1
fi

if ! python3 /opt/pristine/check_statement.py "$FILE" "$NAME" > "$LOG.check" 2>&1; then
  echo "REJECTED: format problems:"
  sed 's/^/  - /' "$LOG.check"
  cat "$LOG.check" >> "$LOG"
  FAIL=1
fi

cp -f "$FILE" "$LOGDIR/$N.lean" 2>/dev/null
if [ "$FAIL" -eq 0 ]; then
  echo "$(date -u +%FT%TZ) $N accepted" >> "$LOGDIR/attempts.log"
  echo "ACCEPTED: the file builds and has the required shape. The statement itself will be assessed by people; keep refining it if you have time left."
else
  echo "$(date -u +%FT%TZ) $N rejected" >> "$LOGDIR/attempts.log"
fi
exit 0
