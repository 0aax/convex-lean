set -u

cd /app/convex-eval

mkdir -p /logs/verifier
: > /logs/verifier/checks.log

# ---------------------------------------------------------------------------
# The comparator is the sole authority on reward: it grades Duchi_Q1_1 in
# LeanWorkspace/Duchi_Q1_1.lean against the trusted challenge, replaying through
# the Lean kernel.
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
STRAY=$( (pgrep -a -x python3; pgrep -a -x python3.12; pgrep -a -x python; pgrep -a -x lean; pgrep -a -x lake; pgrep -a -x sleep; pgrep -a -x node; pgrep -a -x claude; pgrep -a -x codex) 2>/dev/null | grep -vE 'daytona_repl_worker|sleep infinity' || true)
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

# The v4.21 comparator release recurses once per dependency it checks, so a
# Mathlib-scale solution overflows the default 8 MB stack and a correct proof
# would be rejected. 1 GB, or the hard limit if that is lower.
ulimit -s 1048576 2>/dev/null || ulimit -s "$(ulimit -H -s)"

if PATH=/opt/comparator/bin:$PATH lake env comparator /opt/pristine/comparator.json \
     > /logs/verifier/comparator.log 2>&1; then
  echo "comparator accepted a proof of Duchi_Q1_1" >> /logs/verifier/checks.log
  echo 1 > /logs/verifier/reward.txt
else
  echo "comparator rejected" >> /logs/verifier/checks.log
  tail -n 20 /logs/verifier/comparator.log >> /logs/verifier/checks.log
  echo 0 > /logs/verifier/reward.txt
fi

rm -f LeanWorkspace/Challenge.lean
