set -u

cd /app/open-eval

mkdir -p /logs/verifier
: > /logs/verifier/checks.log

# ---------------------------------------------------------------------------
# The comparator is the sole authority on reward, and BOTH passes always run,
# so every trial's verification is uniform: the POS pass grades
# generalized_lax_POS in LeanWorkspace/GeneralizedLax_pos.lean, the NEG
# pass grades generalized_lax_NEG in LeanWorkspace/GeneralizedLax_neg.lean,
# each against the same trusted self-contained challenge. Either acceptance is
# a full solution; both accepting is impossible without an inconsistency, and
# each pass replays through two independent kernels.
#
# The pinned package files are handled by RESTORATION, not rejection: the
# comparator builds both the challenge and the solution inside this workspace,
# so a tampered manifest/toolchain/lakefile would shift both sides of its
# comparison symmetrically.
# ---------------------------------------------------------------------------
for f in lakefile.toml lean-toolchain lake-manifest.json LeanWorkspace.lean; do
  if ! cmp -s "/opt/pristine/$f" "$f"; then
    echo "WARN: $f was modified; pristine copy restored for grading" >> /logs/verifier/checks.log
    cp -f "/opt/pristine/$f" "$f"
  fi
done

# Stop processes the agent left running, so the rebuild below is not slowed by
# them. Daytona's own REPL worker and keep-alive are excluded; nothing started
# by this script is running yet.
STRAY=$( (pgrep -a -x python3; pgrep -a -x python3.12; pgrep -a -x python; pgrep -a -x lean; pgrep -a -x lake; pgrep -a -x sleep; pgrep -a -x node) 2>/dev/null | grep -vE 'daytona_repl_worker|sleep infinity' || true)
if [ -n "$STRAY" ]; then
  echo "NOTE: stopped stray agent processes before grading:" >> /logs/verifier/checks.log
  echo "$STRAY" | sed 's/^/      /' >> /logs/verifier/checks.log
  echo "$STRAY" | awk '{print $1}' | xargs -r kill 2>/dev/null
  sleep 2
  echo "$STRAY" | awk '{print $1}' | xargs -r kill -9 2>/dev/null
fi

rm -rf .lake/build
lake build LeanWorkspace > /logs/verifier/lake_build.log 2>&1 \
  || echo "WARN: lake build failed (advisory; the comparator builds independently)" >> /logs/verifier/checks.log

rm -f LeanWorkspace/Challenge.lean
cp /opt/pristine/Challenge.lean LeanWorkspace/Challenge.lean

POS_OK=1
NEG_OK=1

if PATH=/opt/comparator/bin:$PATH lake env comparator /opt/pristine/comparator.json \
     > /logs/verifier/comparator_pos.log 2>&1; then
  POS_OK=0
  echo "POS: comparator accepted a proof of generalized_lax_POS" >> /logs/verifier/checks.log
else
  echo "POS: comparator rejected" >> /logs/verifier/checks.log
fi

if PATH=/opt/comparator/bin:$PATH lake env comparator /opt/pristine/comparator_neg.json \
     > /logs/verifier/comparator_neg.log 2>&1; then
  NEG_OK=0
  echo "NEG: comparator accepted a proof of generalized_lax_NEG -- the proposition is disproved; audit the statement" >> /logs/verifier/checks.log
else
  echo "NEG: comparator rejected" >> /logs/verifier/checks.log
fi

rm -f LeanWorkspace/Challenge.lean

if [ $POS_OK -eq 0 ] || [ $NEG_OK -eq 0 ]; then
  echo 1 > /logs/verifier/reward.txt
else
  tail -n 20 /logs/verifier/comparator_pos.log >> /logs/verifier/checks.log
  tail -n 20 /logs/verifier/comparator_neg.log >> /logs/verifier/checks.log
  echo 0 > /logs/verifier/reward.txt
fi
