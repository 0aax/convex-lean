#!/usr/bin/env bash
# `submit pos|neg` -- verify a claimed proof with the grader's comparator, in place.
#
# Prints exactly one of two verdict lines. The comparator's output goes to
# /logs/agent/gate/attempts/, along with a copy of the submitted file; on
# acceptance /logs/agent/gate/accepted is written, which the gated agent loop
# reads to end the run. (/logs/agent is downloaded with the trial; /logs/verifier
# is emptied before grading.) Rendered per task from submit_template.sh and
# installed as /usr/local/bin/submit by the Dockerfile.
set -u

REJECT="Your submission did not pass verification. Keep working to find a correct, complete proof."
ACCEPT="Accepted. You may end your turn; the run will finish."
GATE=/logs/agent/gate
ATT=$GATE/attempts

usage() {
  cat <<'USAGE'
usage: submit pos | submit neg

  pos   verify your proof of log_brunn_minkowski_POS in LeanWorkspace/LogBrunnMinkowski_pos.lean
  neg   verify your proof of log_brunn_minkowski_NEG in LeanWorkspace/LogBrunnMinkowski_neg.lean

The check runs the grader's comparator on the file as it is on disk and can
take a few minutes; run it with a generous timeout. It reports only whether the
submission was accepted.
USAGE
}

case "${1:-}" in
  pos) SIDE=pos; CFG=/opt/pristine/comparator.json;     FILE=LeanWorkspace/LogBrunnMinkowski_pos.lean ;;
  neg) SIDE=neg; CFG=/opt/pristine/comparator_neg.json; FILE=LeanWorkspace/LogBrunnMinkowski_neg.lean ;;
  *)   usage; exit 2 ;;
esac

mkdir -p "$ATT"
cd /app/open-eval || { echo "$REJECT"; exit 0; }

# One submission at a time.
exec 9>"$GATE/lock"
flock 9

# Attempts are numbered by their logs, which exist from this point on even if
# the check is killed before a verdict.
N=$(printf '%03d' $(( $(ls "$ATT" 2>/dev/null | grep -c -- '\.log$') + 1 )))
LOG=$ATT/$N-$SIDE.log
: > "$LOG"

verdict() {  # $1 = accepted|rejected
  cp -f "$FILE" "$ATT/$N-$SIDE-$1.lean" 2>/dev/null
  echo "$(date -u +%FT%TZ) $N $SIDE $1" >> "$GATE/attempts.log"
  if [ "$1" = accepted ]; then
    echo "$SIDE" > "$GATE/accepted"
    echo "$ACCEPT"
  else
    echo "$REJECT"
  fi
}

# The pinned package files are restored, as the grader restores them, so the
# verdict here matches the final grade.
for f in lakefile.toml lean-toolchain lake-manifest.json LeanWorkspace.lean; do
  if ! cmp -s "/opt/pristine/$f" "$f"; then
    echo "pinned file $f was modified; pristine copy restored" >> "$LOG"
    cp -f "/opt/pristine/$f" "$f"
  fi
done

# The challenge module is installed only for the duration of the check, and
# removed even if the check is interrupted.
trap 'rm -f LeanWorkspace/Challenge.lean' EXIT
rm -f LeanWorkspace/Challenge.lean
cp /opt/pristine/Challenge.lean LeanWorkspace/Challenge.lean

if PATH=/opt/comparator/bin:$PATH lake env comparator "$CFG" >> "$LOG" 2>&1; then
  verdict accepted
else
  verdict rejected
fi
exit 0
