#!/usr/bin/env bash
# End-to-end check that the comparator toolchain in the base image works, and
# that it rejects the three things the grader relies on it to reject.
#
# Run against a built base image:
#   docker run --rm -v "$PWD/docker/lean-mathlib-base/comparator-smoke.sh:/smoke.sh:ro" \
#     ghcr.io/0aax/open-eval-base:<tag> bash /smoke.sh
set -euxo pipefail

export PATH=/opt/comparator/bin:$PATH
cd /app/open-eval

command -v comparator
command -v lean4export
command -v landrun
command -v nanoda_bin
cat /opt/comparator/PINS

# Non-fatal: says whether Landlock is usable in this container at all, so that a
# comparator failure below can be told apart from a sandbox that never worked.
landrun --best-effort --ro / --rw /dev -ldd -add-exec /bin/true \
  && echo LANDRUN-PROBE-OK || echo LANDRUN-PROBE-FAILED

cat > /tmp/cmp.json <<'JSON'
{"challenge_module": "LeanWorkspace.CmpChallenge",
 "solution_module": "LeanWorkspace.CmpSolution",
 "theorem_names": ["smoke_thm"],
 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
 "enable_nanoda": true}
JSON

# Core Lean only, no Mathlib: keeps the run short and isolates landrun, the
# kernel replay and nanoda from Mathlib-scale export.
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
grep -q "Lean default kernel accepts the solution" /tmp/ok.log
grep -q "Nanoda kernel accepts the solution" /tmp/ok.log

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

echo COMPARATOR-OK
