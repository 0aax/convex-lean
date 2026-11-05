"""A Daytona environment that resumes an EXISTING sandbox instead of creating a
fresh one, so a resumed trial keeps the original sandbox's exact filesystem and
used-disk state (faithful disk), unlike a snapshot resume which starts on a fresh
overlay with the full writable quota free.

Use it by pointing the job config's environment at this class and giving it the
sandbox id:

    "environment": {
      "import_path": "resume_daytona:ResumeDaytonaEnvironment",
      "delete": false,
      "kwargs": { "resume_sandbox_id": "<sandbox-id>" }
    }

Because environment.kwargs is job-wide, one job config carries one sandbox id, so
resume one trial per job.

Mechanism: harbor's _DaytonaStrategy.start() calls env._create_sandbox() once to
set self._sandbox; everything after operates on that handle. This subclass
overrides _create_sandbox to `daytona.get(id)` the existing sandbox and, when it
is not already running, `start()` it, in place of `daytona.create(params)`. The
params harbor computed (image/snapshot, resources) are ignored on purpose.

Default is stop-then-start (`--ek resume_reset_state=false` to skip): stopping a
container sandbox clears memory and kills leftover processes while preserving the
filesystem, giving the resumed agent a clean process slate. The crashed instance
is mutated in place, so snapshot it first if you want a fallback.
"""
from __future__ import annotations

from harbor.environments.daytona.environment import DaytonaEnvironment

_RUNNING = "started"
# A plain start() brings these up (archived is restored from object storage).
_STARTABLE = {"stopped", "archived"}
# Terminal/bad states: fail with a clear message rather than a cryptic start().
_UNUSABLE = {"destroyed", "destroying", "error", "build_failed"}

# In-place tidy: move the previous run's gate/ (incl. the `accepted` flag) and
# stream files under /logs/agent/prev/<ts>/, then drop truncated trailing lines
# from every session/subagent jsonl so `claude --resume` does not merge its first
# new record into a broken line. Runs in the reused sandbox before harbor proceeds.
_TIDY_SH = r"""
set -e
ts=$(date -u +%Y%m%dT%H%M%SZ)
p=/logs/agent/prev/$ts
mkdir -p "$p"
for f in /logs/agent/gate /logs/agent/claude-code*.txt /logs/agent/trajectory.json; do
  [ -e "$f" ] && mv "$f" "$p"/ && echo "moved $(basename "$f")"
done
python3 - <<'PY'
import glob, json, os
paths = sorted(glob.glob('/logs/agent/sessions/projects/*/*.jsonl') +
               glob.glob('/logs/agent/sessions/projects/*/*/subagents/*.jsonl'))
for path in paths:
    lines = open(path,'rb').read().split(b'\n')
    if lines and lines[-1] == b'': lines.pop()
    bad = 0
    while lines:
        try: json.loads(lines[-1]); break
        except Exception: lines.pop(); bad += 1
    if bad:
        tmp = path + '.trim'
        open(tmp,'wb').write(b'\n'.join(lines) + (b'\n' if lines else b''))
        os.replace(tmp, path)
        print('trimmed %d line(s): %s' % (bad, path))
print('trim done (%d files)' % len(paths))
PY
"""


def _shq(s: str) -> str:
    return "'" + s.replace("'", "'\\''") + "'"


def _state(sandbox) -> str:
    s = getattr(sandbox, "state", None)
    return str(getattr(s, "value", s) or "").lower()


class ResumeDaytonaEnvironment(DaytonaEnvironment):
    def __init__(self, *args, **kwargs):
        # Pull our kwargs out of environment.kwargs before harbor's __init__,
        # which forwards the rest and rejects nothing (it takes **kwargs).
        self._resume_sandbox_id = kwargs.pop("resume_sandbox_id", None)
        reset = kwargs.pop("resume_reset_state", True)
        self._resume_reset_state = str(reset).strip().lower() not in ("false", "0", "no")
        tidy = kwargs.pop("resume_tidy", True)
        self._resume_tidy = str(tidy).strip().lower() not in ("false", "0", "no")
        super().__init__(*args, **kwargs)
        if not self._resume_sandbox_id:
            raise ValueError(
                "ResumeDaytonaEnvironment requires environment.kwargs.resume_sandbox_id"
            )

    async def _create_sandbox(self, params, daytona=None):  # type: ignore[override]
        if daytona is None:
            if not self._client_manager:
                raise RuntimeError("Client manager not initialized.")
            daytona = await self._client_manager.get_client()

        sid = self._resume_sandbox_id
        self.logger.info(f"resume: attaching to existing sandbox {sid}")
        sandbox = await daytona.get(sid)
        st = _state(sandbox)
        self.logger.info(f"resume: sandbox {sid} state={st}")
        if st in _UNUSABLE:
            raise RuntimeError(
                f"resume: sandbox {sid} is in unusable state {st!r}; cannot resume "
                "(it may have been deleted or errored)"
            )

        if self._resume_reset_state and st == _RUNNING:
            # Clean process slate: stop (clears memory, keeps filesystem) then start.
            self.logger.info(f"resume: stopping {sid} to clear memory/processes")
            await sandbox.stop()
            await sandbox.wait_for_sandbox_stop(timeout=0)
            st = _state(await daytona.get(sid))

        if st != _RUNNING:
            self.logger.info(f"resume: starting {sid} (state={st})")
            await sandbox.start(timeout=0)
            await sandbox.wait_for_sandbox_start(timeout=0)

        self._sandbox = sandbox
        self.logger.info(f"resume: sandbox {sid} ready, state={_state(await daytona.get(sid))}")

        if self._resume_tidy:
            await self._resume_tidy_state()

    # Move the previous run's gate directory (cycles.jsonl AND the `accepted`
    # flag, which would otherwise make the gate stop on cycle 1) and stream files
    # aside, and drop any truncated trailing lines from the session jsonl. This
    # is the in-place equivalent of tidying and trimming a sandbox snapshot;
    # snapshot resume gets it from the staged snapshot, in-place needs it here.
    async def _resume_tidy_state(self) -> None:
        if not self._sandbox:
            raise RuntimeError("resume: sandbox not attached before tidy")
        self.logger.info("resume: tidying prior gate/stream state and trimming session tail")
        r = await self._sandbox.process.exec("bash -c " + _shq(_TIDY_SH), timeout=300)
        out = (getattr(r, "result", None) or "").strip()
        if out:
            for ln in out.splitlines():
                self.logger.info("resume-tidy: " + ln)
        code = getattr(r, "exit_code", None)
        if code not in (0, None):
            raise RuntimeError(f"resume tidy failed (exit {code}): {out[-400:]}")
