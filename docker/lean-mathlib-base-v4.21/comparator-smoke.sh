#!/usr/bin/env bash
# End-to-end check that the comparator toolchain in the base image works, and
# that it rejects the three things the grader relies on it to reject.
#
# Run against a built base image:
#   docker run --rm -v "$PWD/docker/lean-mathlib-base-v4.21/comparator-smoke.sh:/smoke.sh:ro" \
#     ghcr.io/0aax/open-eval-base:<tag> bash /smoke.sh
#
# v4.21 image: its comparator release has no nanoda, so only the Lean kernel
# replay is checked.
set -euxo pipefail

export PATH=/opt/comparator/bin:$PATH
cd /app/open-eval

command -v comparator
command -v lean4export
command -v landrun
cat /opt/comparator/PINS

# Non-fatal: says whether Landlock is usable in this container at all, so that a
# comparator failure below can be told apart from a sandbox that never worked.
landrun --best-effort --ro / --rw /dev -ldd -add-exec /bin/true \
  && echo LANDRUN-PROBE-OK || echo LANDRUN-PROBE-FAILED

cat > /tmp/cmp.json <<'JSON'
{"challenge_module": "LeanWorkspace.CmpChallenge",
 "solution_module": "LeanWorkspace.CmpSolution",
 "theorem_names": ["smoke_thm"],
 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
JSON

# Core Lean only, no Mathlib: keeps the run short and isolates landrun and the
# kernel replay from Mathlib-scale export.
cat > LeanWorkspace/CmpChallenge.lean <<'LEAN'
def smokeAdd (n : Nat) : Nat := n + 1

theorem smoke_thm : ∀ n : Nat, 0 < smokeAdd n := by sorry
LEAN

run_comparator() { lake env comparator /tmp/cmp.json; }

# 1. an honest proof of the challenge statement is accepted
cat > LeanWorkspace/CmpSolution.lean <<'LEAN'
def smokeAdd (n : Nat) : Nat := n + 1

theorem smoke_thm : ∀ n : Nat, 0 < smokeAdd n := by unfold smokeAdd; omega
LEAN
run_comparator | tee /tmp/ok.log
grep -q "Solution valid." /tmp/ok.log

# 2. sorry is rejected: sorryAx is not a permitted axiom
cat > LeanWorkspace/CmpSolution.lean <<'LEAN'
def smokeAdd (n : Nat) : Nat := n + 1

theorem smoke_thm : ∀ n : Nat, 0 < smokeAdd n := by sorry
LEAN
if run_comparator; then echo "comparator accepted a sorry"; exit 1; fi

# 3. proving something else is rejected
cat > LeanWorkspace/CmpSolution.lean <<'LEAN'
def smokeAdd (n : Nat) : Nat := n + 1

theorem smoke_thm : True := trivial
LEAN
if run_comparator; then echo "comparator accepted a different statement"; exit 1; fi

# 4. the real point: same statement text, same proof text, honest proof -- but
#    over a weakened definition. Rejected on the dependency closure. This is the
#    exploit class the grader's textual statement check cannot see.
cat > LeanWorkspace/CmpSolution.lean <<'LEAN'
def smokeAdd (n : Nat) : Nat := n + 2

theorem smoke_thm : ∀ n : Nat, 0 < smokeAdd n := by unfold smokeAdd; omega
LEAN
if run_comparator; then echo "comparator accepted a weakened definition"; exit 1; fi

# 5. an honest Mathlib-scale proof is accepted. This comparator release recurses
#    once per dependency it checks; this one-liner's closure already overflows the
#    default 8 MB stack (and 16 MB), so it checks that the stack limit the tasks'
#    test.sh/submit.sh set can be raised in this container and is enough.
ulimit -s 1048576 2>/dev/null || ulimit -s "$(ulimit -H -s)"
ulimit -s
cat > LeanWorkspace/CmpChallenge.lean <<'LEAN'
import Mathlib

theorem smoke_thm : ∫ x in (0:ℝ)..1, x = 1 / 2 := by sorry
LEAN
cat > LeanWorkspace/CmpSolution.lean <<'LEAN'
import Mathlib

theorem smoke_thm : ∫ x in (0:ℝ)..1, x = 1 / 2 := by norm_num [integral_id]
LEAN
run_comparator | tee /tmp/ok-mathlib.log
grep -q "Solution valid." /tmp/ok-mathlib.log

echo COMPARATOR-OK
