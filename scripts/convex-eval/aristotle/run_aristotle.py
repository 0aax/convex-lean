#!/usr/bin/env python3
r"""Run the textbook tasks through Aristotle, --max-active projects at a time.

    uv run --no-project --with aristotlelib==2.1.0 python -s scripts/convex-eval/aristotle/run_aristotle.py \
        --projects-dir aristotle/projects --out-dir jobs/aristotle-convex-eval-v28-2h

Keeps a window of --max-active projects (default 5, API cap 15) in flight:
submit until the window is full, poll every two minutes, and when a project
finishes download its tarball and submit the next pending task into the freed
slot. State is checkpointed to <out-dir>/state.json after every change, so
re-running the same command re-attaches to the projects in flight instead of
resubmitting them. Ctrl-C stops submitting; it never cancels server-side work.

Requires `aristotlelib` 2.1.0 and an API key in ARISTOTLE_API_KEY (or
--env-file). Run it with --no-project and -s, as above, so no other copy of the
SDK shadows the pinned one. The SDK is task-centric: a project only reports
RUNNING/IDLE, the lifecycle lives on its AgentTask via `project.get_tasks()`,
and results come from `project.get_files()`; the shims `_status_of`,
`_refresh`, `_cancel` and `_download` also accept the older 0.7.x surface.
"""

from __future__ import annotations

import argparse
import asyncio
import json
import logging
import os
import re
import signal
import subprocess
import sys
import tarfile
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from text_checks import grade_text  # the task verifier's text checks

try:
    import aristotlelib
    from aristotlelib import Project, ProjectStatus
    from aristotlelib.api_request import AristotleAPIError
except ImportError:
    sys.exit("aristotlelib is not installed. Try: uv run --no-project --with aristotlelib==2.1.0 python -s scripts/convex-eval/aristotle/run_aristotle.py")


log = logging.getLogger("run_aristotle")

# Statuses that mean the server is done with a project; any other still occupies a slot.
TERMINAL = {
    "COMPLETE",
    "COMPLETE_WITH_ERRORS",
    "OUT_OF_BUDGET",
    "FAILED",
    "CANCELED",
}
# Terminal states whose tarball is still worth downloading (partial progress counts).
HAS_SOLUTION = {"COMPLETE", "COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET"}
# Server-side faults, as opposed to Aristotle failing to find a proof: the only
# ones worth another attempt.
RETRYABLE = {"FAILED"}

STATE_VERSION = 1

# Wait before retrying a refused submit; shorter than --poll-interval, since a
# refusal means a slot freed up sooner than we noticed.
SUBMIT_RETRY_BACKOFF = 60.0


# --------------------------------------------------------------------------
# state


class State:
    """The run's checkpoint: one record per task, flushed on every change.

    Written atomically (temp file + replace) so a kill mid-write cannot strand
    the project ids of work already running and paid for.
    """

    def __init__(self, path: Path, prompt: str, projects_dir: Path):
        self.path = path
        self.prompt = prompt
        self.projects_dir = str(projects_dir)
        self.tasks: dict[str, dict] = {}

    @classmethod
    def load_or_new(cls, path: Path, prompt: str, projects_dir: Path) -> "State":
        st = cls(path, prompt, projects_dir)
        if not path.exists():
            return st
        raw = json.loads(path.read_text(encoding="utf-8"))
        if raw.get("version") != STATE_VERSION:
            raise SystemExit(
                f"{path} has state version {raw.get('version')}, expected "
                f"{STATE_VERSION}. Move it aside to start a fresh run."
            )
        st.tasks = raw.get("tasks", {})
        if raw.get("prompt") != prompt:
            log.warning(
                "resuming a run whose prompt differs from --prompt; already "
                "submitted tasks keep the original prompt"
            )
        return st

    def save(self) -> None:
        payload = {
            "version": STATE_VERSION,
            "prompt": self.prompt,
            "projects_dir": self.projects_dir,
            "updated_at": _now(),
            "tasks": self.tasks,
        }
        tmp = self.path.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        tmp.replace(self.path)

    def rec(self, task: str) -> dict:
        return self.tasks.setdefault(
            task,
            {
                "project_id": None,
                "status": None,
                "attempts": 0,
                "submitted_at": None,
                "finished_at": None,
                "solution": None,
                "lean": None,
                "has_sorry": None,
                "grade_fails": None,
                "lean_errors": None,
                "total_sec": None,
                "work_sec": None,
                "queue_sec": None,
                "work_source": None,
                "event_work_sec": None,
                "event_count": None,
                "event_timed_count": None,
                "events_truncated": None,
                "observed_started_at": None,
                "observed_sec": None,
                "error": None,
            },
        )

    def is_finished(self, task: str) -> bool:
        r = self.tasks.get(task)
        return bool(r and r.get("status") in TERMINAL and not r.get("_requeue"))

    def in_flight(self) -> dict[str, dict]:
        return {
            t: r
            for t, r in self.tasks.items()
            if r.get("project_id") and r.get("status") not in TERMINAL
        }


def _now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _fmt_dur(seconds) -> str:
    if seconds is None:
        return "unknown"
    seconds = int(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f"{h}h{m:02d}m" if h else (f"{m}m{s:02d}s" if m else f"{s}s")


def _fmt_timing(rec: dict) -> str:
    """`work (+queue queued)`, falling back to the total when unsplit."""
    if rec.get("work_sec") is None:
        return _fmt_dur(rec.get("total_sec") or rec.get("observed_sec"))
    queued = rec.get("queue_sec") or 0
    tilde = "~" if rec.get("work_source") == "observed" else ""
    out = f"{tilde}{_fmt_dur(rec['work_sec'])}"
    if queued >= 60:
        out += f" (+{_fmt_dur(queued)} queued)"
    if rec.get("event_work_sec") is not None:
        out += f" [events {_fmt_dur(rec['event_work_sec'])}]"
    return out


# --------------------------------------------------------------------------
# SDK compatibility shims


def _enum_name(value) -> str:
    """Uppercase name of an enum-ish status, however the SDK spells it.

    Read `.name`, never `.value`: 2.x ProjectStatus is an IntEnum.
    """
    if value is None:
        return "UNKNOWN"
    name = getattr(value, "name", None)
    if isinstance(name, str):
        return name.upper()
    return str(getattr(value, "value", value)).upper()


def _status_of(project) -> str:
    """Normalise a project's status to a plain uppercase string.

    2.x keeps the lifecycle on the AgentTask and leaves the project with only
    RUNNING/IDLE, so there we report the newest task's status, cached by `_refresh`.
    """
    name = _enum_name(getattr(project, "status", None))
    if name in ("RUNNING", "IDLE"):  # 2.x, task-centric
        return _LATEST_TASK_STATUS.get(project.project_id, "UNKNOWN")
    return name


_LATEST_TASK_STATUS: dict[str, str] = {}
# project_id -> (created_at, last_updated_at) of its newest AgentTask, on 2.x.
_LATEST_TASK_TIMES: dict[str, tuple] = {}


def _as_dt(value):
    """Coerce a timestamp field to an aware datetime, or None."""
    if value is None:
        return None
    if isinstance(value, str):
        try:
            value = datetime.fromisoformat(value.replace("Z", "+00:00"))
        except ValueError:
            return None
    if not isinstance(value, datetime):
        return None
    # Assume UTC for naive datetimes, which is what the API serves.
    return value if value.tzinfo else value.replace(tzinfo=timezone.utc)


def _endpoints_of(obj) -> tuple:
    """(created_at, end) for an object, or (None, None). The end field is
    `last_updated_at` on 0.7.x Project and 2.x AgentTask, `last_updated` on 2.x Project.
    """
    start = _as_dt(getattr(obj, "created_at", None))
    for field in ("last_updated_at", "last_updated"):
        end = _as_dt(getattr(obj, field, None))
        if end is not None:
            return start, end
    return start, None


def _secs(start, end) -> float | None:
    if start is None or end is None:
        return None
    return max(0.0, (end - start).total_seconds())  # clamp any clock skew


def _total_endpoints(project) -> tuple:
    """Submission-to-finish endpoints, preferring the 2.x AgentTask's."""
    times = _LATEST_TASK_TIMES.get(project.project_id)
    if times is not None:
        return times
    return _endpoints_of(project)


EVENT_PAGE = 50
# Backstop against paging an unbounded event log; a truncated walk is flagged.
MAX_EVENT_PAGES = 40


async def _event_timing(project) -> dict | None:
    """Walk a task's event log once for two timing reads.

    `first` is the earliest event timestamp: the project sits in QUEUED after
    `created_at`, so the first event marks the queue/work boundary.
    `duration_sum` totals the per-event `duration_seconds` Aristotle reports,
    its own accounting rather than a wall-clock span; `timed`/`count` say how
    completely the events cover the run. 0.7.x has no events API and returns None.
    """
    if not hasattr(project, "get_tasks"):
        return None
    try:
        tasks, _ = await project.get_tasks(limit=1)
        if not tasks or not hasattr(tasks[0], "get_events"):
            return None
        task = tasks[0]

        first, duration_sum, count, timed = None, 0.0, 0, 0
        key, pages, truncated = None, 0, False
        while True:
            events, key = await task.get_events(
                pagination_key=key, limit=EVENT_PAGE, newest_first=False
            )
            for event in events:
                count += 1
                # Take the min rather than trusting page order.
                stamp = _as_dt(getattr(event, "created_at", None))
                if stamp is not None and (first is None or stamp < first):
                    first = stamp
                secs = getattr(event, "duration_seconds", None)
                if isinstance(secs, (int, float)) and not isinstance(secs, bool):
                    if secs >= 0:
                        duration_sum += float(secs)
                        timed += 1
            pages += 1
            if not key:
                break
            if pages >= MAX_EVENT_PAGES:
                truncated = True
                break
        if not count:
            return None
        return {
            "first": first,
            "duration_sum": duration_sum,
            "count": count,
            "timed": timed,
            "truncated": truncated,
        }
    except AristotleAPIError:
        return None


async def _refresh(project) -> str:
    """Refresh a project in place and return its normalised status."""
    await project.refresh()
    if hasattr(project, "get_tasks"):  # 2.x: status lives on the task
        try:
            tasks, _ = await project.get_tasks(limit=1)
            if tasks:
                _LATEST_TASK_STATUS[project.project_id] = _enum_name(tasks[0].status)
                ends = _endpoints_of(tasks[0])
                if ends[0] is not None:
                    _LATEST_TASK_TIMES[project.project_id] = ends
        except AristotleAPIError:
            pass  # fall back to whatever the project itself reports
    return _status_of(project)


async def _cancel(project) -> None:
    """Stop a project's server-side work. 0.7.x cancels the project; 2.x cancels
    the newest AgentTask.
    """
    canceller = getattr(project, "cancel", None)
    if canceller is not None:  # 0.7.x
        await canceller()
        return
    tasks, _ = await project.get_tasks(limit=1)  # 2.x
    if not tasks:
        raise AristotleAPIError(f"project {project.project_id} has no task to cancel")
    await tasks[0].cancel()


async def _download(project, destination: Path) -> Path:
    """Download the result tarball, under whichever name the SDK gives it.

    2.x `get_files` re-serves the input archive when the project has no result
    and reports success. That input is our own sorry-ed project, so it is
    refused rather than saved as a solution. 0.7.x `get_solution` simply errors.
    """
    getter = getattr(project, "get_solution", None)
    if getter is None:
        await project.refresh()
        if not getattr(project, "has_files", True):
            raise AristotleAPIError(
                f"project {project.project_id} has no result files; refusing "
                "to download the input archive in their place"
            )
        getter = project.get_files
    return Path(await getter(destination=str(destination)))


# --------------------------------------------------------------------------
# work


def discover_tasks(projects_dir: Path, only: list[str] | None) -> list[str]:
    """Every subdirectory that looks like a Lean project, in stable order."""
    found = sorted(
        p.name
        for p in projects_dir.iterdir()
        if p.is_dir() and (p / "lakefile.toml").exists()
    )
    if only is None:
        return found
    missing = [t for t in only if t not in found]
    if missing:
        raise SystemExit(
            f"not present in {projects_dir}: {', '.join(sorted(missing))}"
        )
    # Preserve the caller's ordering so --tasks doubles as a priority list.
    return [t for t in only if t in found]


def _grade(lean: Path, project_dir: Path, task: str) -> list[str]:
    """The harbor verifier's text checks, applied to Aristotle's returned file.

    The reference is the statement file we submitted, which the answer must
    have preserved: a `sorry`-free file that redefines the given definitions and
    proves a different theorem fails here. Returns the FAIL reasons, empty when
    the text checks pass; compilation is the other half of the verdict
    (--verify-lean).
    """
    ref = project_dir / "LeanWorkspace" / f"{task}.lean"
    if not ref.exists():
        return [f"reference statement not found: {ref}"]
    return grade_text(
        lean.read_text(encoding="utf-8", errors="replace"),
        ref.read_text(encoding="utf-8"),
        task,
    )


def extract_lean(tarball: Path, dest_dir: Path, task: str) -> Path | None:
    """Pull `<task>.lean` out of a result tarball.

    Members are matched by basename and read through the tar's own file object,
    so an odd archive cannot write outside dest_dir.
    """
    want = f"{task}.lean"
    try:
        with tarfile.open(tarball, "r:gz") as tf:
            members = [
                m
                for m in tf.getmembers()
                if m.isfile() and Path(m.name).name == want
            ]
            if not members:
                return None
            # Prefer the shallowest match; deeper copies tend to be scratch dirs.
            member = min(members, key=lambda m: len(Path(m.name).parts))
            src = tf.extractfile(member)
            if src is None:
                return None
            data = src.read()
    except (tarfile.TarError, OSError) as exc:
        log.warning("%s: could not read %s (%s)", task, tarball.name, exc)
        return None

    dest_dir.mkdir(parents=True, exist_ok=True)
    out = dest_dir / want
    out.write_bytes(data)
    return out


class Runner:
    def __init__(self, args, state: State, tasks: list[str]):
        self.args = args
        self.state = state
        self.scope = list(tasks)
        self.pending = [t for t in tasks if not state.is_finished(t)]
        self.active: dict[str, Project] = {}
        self.stopping = False
        self.solutions = Path(args.out_dir) / "solutions"
        self.lean_dir = Path(args.out_dir) / "lean"
        self.solutions.mkdir(parents=True, exist_ok=True)
        self.deadline = (
            time.monotonic() + args.task_timeout if args.task_timeout else None
        )

    # -- slots ------------------------------------------------------------

    async def reserved_slots(self) -> int:
        """Slots taken by projects this run did not start: the cap is per account,
        so another run's projects count against the budget up front.
        """
        if not self.args.reserve_existing or self.args.dry_run:
            return 0
        mine = {r["project_id"] for r in self.state.tasks.values() if r.get("project_id")}
        # Which members mean "still occupying a slot" depends on the SDK (0.7.x spells
        # out the lifecycle, 2.x collapses it to RUNNING); select by name so both give
        # a non-empty filter.
        active = {"RUNNING", "NOT_STARTED", "QUEUED", "IN_PROGRESS"}
        active_statuses = [s for s in ProjectStatus if s.name.upper() in active]
        if not active_statuses:
            log.warning(
                "ProjectStatus has no recognised active member (%s); skipping "
                "the check for projects started outside this run",
                ", ".join(s.name for s in ProjectStatus),
            )
            return 0
        try:
            projects, _ = await Project.list_projects(status=active_statuses, limit=100)
        except AristotleAPIError as exc:
            log.warning("could not list existing projects (%s); assuming none", exc)
            return 0
        foreign = [p for p in projects if p.project_id not in mine]
        if foreign:
            log.warning(
                "%d project(s) already active on this account are not part of "
                "this run; reserving those slots",
                len(foreign),
            )
        return len(foreign)

    # -- one task ---------------------------------------------------------

    def _prompt_for(self, project_dir: Path) -> str:
        """The task's own instruction.md, falling back to --prompt.

        Each project carries the harbor task's instruction with the paths rewritten
        to this layout, so Aristotle is told the same rules the harbor agent is
        given and test.sh enforces (which file is graded, what must survive
        verbatim, no axiom or native_decide). The fallback keeps older project
        directories working.
        """
        inst = project_dir / "instruction.md"
        if inst.is_file():
            text = inst.read_text(encoding="utf-8").strip()
            if text:
                return text
        log.warning("%s has no instruction.md; submitting the generic --prompt",
                    project_dir.name)
        return self.args.prompt

    async def submit(self, task: str) -> bool:
        rec = self.state.rec(task)
        project_dir = Path(self.args.projects_dir) / task

        if self.args.dry_run:
            log.info("[dry-run] would submit %s from %s", task, project_dir)
            return True


        try:
            project = await Project.create_from_directory(
                prompt=self._prompt_for(project_dir), project_dir=str(project_dir)
            )
        except AristotleAPIError as exc:
            # A rejected create means our slot accounting is behind the server's;
            # leave the task pending for the next loop iteration.
            log.warning("submit %s failed (status %s): %s", task, exc.status_code, exc)
            rec["error"] = f"submit: {exc}"
            self.state.save()
            return False

        rec.update(
            project_id=project.project_id,
            status=_status_of(project),
            attempts=rec["attempts"] + 1,
            submitted_at=_now(),
            finished_at=None,
            solution=None,
            lean=None,
            has_sorry=None,
            total_sec=None,
            work_sec=None,
            queue_sec=None,
            work_source=None,
            event_work_sec=None,
            event_count=None,
            event_timed_count=None,
            events_truncated=None,
            observed_started_at=None,
            observed_sec=None,
            error=None,
        )
        rec.pop("_requeue", None)
        self.state.save()  # before anything else can fail: never lose an id
        self.active[task] = project
        log.info("submitted %s -> %s", task, project.project_id)
        return True

    async def record_timing(self, rec: dict, project) -> None:
        """Split submission-to-finish into queue time and agent time.

        `created_at` is stamped at submission and the project then sits in QUEUED,
        so the server's span is queue plus work; the fields are kept separate so a
        long queue is never read as a slow proof. `work_source` says how the
        boundary was found: "events" (2.x, the first event's timestamp, accurate),
        "observed" (the poll that first saw IN_PROGRESS, coarse to --poll-interval),
        or None (only total_sec is meaningful).
        """
        start, end = _total_endpoints(project)
        total = _secs(start, end)
        rec["total_sec"] = total

        # Measure the queue and subtract: a duration is comparable across clocks, an
        # instant is not (the observed boundary is our clock, `end` the server's).
        # Aristotle's own per-step accounting is kept beside the span; it only tiles
        # the run if every step emits a timed event, so the event counts are kept too.
        events = await _event_timing(project)
        if events:
            rec["event_work_sec"] = events["duration_sum"]
            rec["event_count"] = events["count"]
            rec["event_timed_count"] = events["timed"]
            rec["events_truncated"] = events["truncated"]
            if events["truncated"]:
                log.warning(
                    "%s: stopped after %d event pages; event_work_sec is a "
                    "partial sum",
                    rec.get("project_id"),
                    MAX_EVENT_PAGES,
                )

        queue, source = None, None
        event_start = events["first"] if events else None
        if event_start is not None and start is not None:
            queue, source = _secs(start, event_start), "events"
        else:
            observed = _secs(
                _as_dt(rec.get("submitted_at")), _as_dt(rec.get("observed_started_at"))
            )
            if observed is not None:
                queue, source = observed, "observed"

        rec["work_source"] = source
        if queue is not None and total is not None:
            queue = min(queue, total)  # a queue cannot outlast the run
            rec["queue_sec"] = queue
            rec["work_sec"] = max(0.0, total - queue)
        else:
            rec["queue_sec"] = queue

        # Our own wall-clock, kept only as a floor: it rounds up to the poll interval
        # and counts time the runner was stopped.
        rec["observed_sec"] = _secs(
            _as_dt(rec.get("submitted_at")), _as_dt(rec.get("finished_at"))
        )

    async def poll_one(self, task: str, project: Project) -> None:
        rec = self.state.rec(task)
        try:
            status = await _refresh(project)
        except AristotleAPIError as exc:
            # Transient: keep the project in the window and try again next tick.
            rec["error"] = f"poll: {exc}"
            log.debug("poll %s failed: %s", task, exc)
            return

        rec["status"] = status
        rec["error"] = None

        if status not in TERMINAL:
            # The only queue/work boundary 0.7.x offers; accurate to one poll interval.
            if status == "IN_PROGRESS" and not rec.get("observed_started_at"):
                rec["observed_started_at"] = _now()
            self.state.save()
            return

        rec["finished_at"] = _now()
        await self.record_timing(rec, project)
        del self.active[task]

        if status in HAS_SOLUTION:
            try:
                path = await _download(project, self.solutions / f"{task}.tar.gz")
                rec["solution"] = str(Path(path).resolve())
                if self.args.extract:
                    lean = extract_lean(Path(path), self.lean_dir, task)
                    rec["lean"] = str(lean.resolve()) if lean else None
                    if lean is None:
                        log.warning("%s: no %s.lean in the result tarball", task, task)
                    else:
                        # Recorded for every task: a COMPLETE whose file fails the
                        # verifier is not a proof (an echoed input, an empty edit,
                        # a rewritten statement).
                        fails = _grade(
                            lean, Path(self.args.projects_dir) / task, task
                        )
                        rec["grade_fails"] = fails
                        rec["has_sorry"] = any(
                            f.startswith("sorry/admit") for f in fails
                        )
                        if fails and status == "COMPLETE":
                            log.warning(
                                "%s: status COMPLETE but %s.lean fails the "
                                "verifier (%s) -- treat as unproved",
                                task,
                                task,
                                "; ".join(fails),
                            )
            except AristotleAPIError as exc:
                # Done server-side; only the fetch failed. Recorded so it can be
                # re-fetched without redoing the proof.
                rec["error"] = f"download: {exc}"
                log.error("download %s failed: %s", task, exc)

        log.info(
            "finished %s: %s in %s%s",
            task,
            status,
            _fmt_timing(rec),
            f" -> {Path(rec['solution']).name}" if rec.get("solution") else "",
        )

        if status in RETRYABLE and rec["attempts"] < self.args.max_attempts:
            log.info(
                "%s hit a server-side failure; requeueing (attempt %d/%d)",
                task,
                rec["attempts"] + 1,
                self.args.max_attempts,
            )
            rec["_requeue"] = True
            self.pending.append(task)

        self.state.save()

    # -- loop -------------------------------------------------------------

    async def run(self) -> int:
        reserved = await self.reserved_slots()
        budget = max(0, self.args.max_active - reserved)
        if budget == 0:
            log.error(
                "no slots available (--max-active %d, %d reserved)",
                self.args.max_active,
                reserved,
            )
            return 1

        # Re-attach to anything a previous run left in flight before submitting.
        for task, rec in self.state.in_flight().items():
            try:
                self.active[task] = await Project.from_id(rec["project_id"])
                log.info("re-attached %s -> %s", task, rec["project_id"])
            except AristotleAPIError as exc:
                log.warning("could not re-attach %s: %s", task, exc)
            if task in self.pending:
                self.pending.remove(task)

        total = len(self.scope)
        log.info(
            "%d task(s) to run, %d already in flight, window of %d",
            len(self.pending),
            len(self.active),
            budget,
        )

        while (self.pending and not self.stopping) or self.active:
            # Fill the window. A failed submit leaves the task pending and breaks
            # out; the shorter retry backoff below covers the wait.
            submit_blocked = False
            while self.pending and len(self.active) < budget and not self.stopping:
                task = self.pending.pop(0)
                if not await self.submit(task):
                    self.pending.insert(0, task)
                    submit_blocked = True
                    break
                if self.args.dry_run:
                    continue

            if self.args.dry_run:
                break

            if not self.active:
                if self.stopping or not self.pending:
                    break
                # Nothing in flight but work left over: every submit is failing.
                log.warning("no active projects and submits are failing; backing off")

            # A rejected submit means a slot is probably already free; retry sooner
            # than the poll interval.
            delay = self.args.poll_interval
            if submit_blocked:
                delay = min(delay, SUBMIT_RETRY_BACKOFF)
            await asyncio.sleep(delay)
            if self.stopping and not self.active:
                break

            # Poll the window with a little concurrency: enough to keep a tick short
            # without refreshing a full window as a burst.
            sem = asyncio.Semaphore(5)

            async def guarded(t, p):
                async with sem:
                    await self.poll_one(t, p)

            await asyncio.gather(
                *(guarded(t, p) for t, p in list(self.active.items()))
            )

            if self.deadline and time.monotonic() > self.deadline:
                log.error("--task-timeout reached; leaving remaining work running")
                break

            self.report(total)

        self.state.save()
        self.report(total, final=True)
        return 0

    def report(self, total: int, final: bool = False) -> None:
        done = [
            self.state.tasks[t]
            for t in self.scope
            if self.state.tasks.get(t, {}).get("status") in TERMINAL
        ]
        ok = sum(1 for r in done if r.get("status") == "COMPLETE")
        partial = sum(
            1 for r in done if r.get("status") in ("COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET")
        )
        bad = len(done) - ok - partial
        line = (
            f"{len(done)}/{total} done "
            f"(complete {ok}, partial {partial}, failed/canceled {bad}) | "
            f"active {len(self.active)} | pending {len(self.pending)}"
        )
        log.info("== %s ==" if final else "-- %s", line)
        if final:
            work = [r["work_sec"] for r in done if r.get("work_sec") is not None]
            queue = [r["queue_sec"] for r in done if r.get("queue_sec") is not None]
            if work:
                log.info(
                    "== agent time over %d task(s): %s total, %s median, "
                    "%s longest%s ==",
                    len(work),
                    _fmt_dur(sum(work)),
                    _fmt_dur(sorted(work)[len(work) // 2]),
                    _fmt_dur(max(work)),
                    f" | {_fmt_dur(sum(queue))} queued" if queue else "",
                )


# --------------------------------------------------------------------------
# cli


def load_env_file(path: Path) -> None:
    """Minimal KEY=VALUE loader, matching how the harbor runs take --env-file."""
    if not path.exists():
        raise SystemExit(f"--env-file not found: {path}")
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, value = line.partition("=")
        os.environ.setdefault(key.strip(), value.strip().strip("'\""))


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    # the repo root
    repo = Path(__file__).resolve().parents[3]
    p = argparse.ArgumentParser(
        description="Submit convex-eval Lean projects to Aristotle, --max-active at a time.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    p.add_argument(
        "--projects-dir",
        type=Path,
        default=repo / "aristotle" / "projects",
        help="directory of per-task Lean projects (aristotle/projects)",
    )
    p.add_argument(
        "--out-dir",
        type=Path,
        default=repo / "jobs" / "aristotle-convex-eval-v28-2h",
        help="where state.json, solutions/, and lean/ are written",
    )
    p.add_argument(
        "--prompt",
        default="Fill in all the sorries in this project.",
        help="instruction sent with every project",
    )
    p.add_argument(
        "--max-active",
        type=int,
        default=5,
        help="projects in flight at once; the API caps this at 15",
    )
    p.add_argument(
        "--verify-lean",
        type=Path,
        metavar="PROJECT",
        help="after (or instead of) running, compile every extracted proof "
             "against this built Lake project -- the half of the harbor verdict "
             "the text checks cannot give",
    )
    p.add_argument(
        "--poll-interval",
        type=float,
        default=120.0,
        help="seconds between status checks of the in-flight window; sized for "
             "slot-refill latency, not detection",
    )
    p.add_argument(
        "--max-attempts",
        type=int,
        default=2,
        help="resubmits for server-side FAILED (not for unproved theorems)",
    )
    p.add_argument(
        "--task-timeout",
        type=float,
        default=0.0,
        help="stop the run after this many seconds; 0 disables",
    )
    p.add_argument(
        "--tasks",
        help="comma-separated task names, or @file with one per line",
    )
    p.add_argument("--limit", type=int, help="run only the first N pending tasks")
    p.add_argument(
        "--no-reserve-existing",
        dest="reserve_existing",
        action="store_false",
        help="do not count other active projects on the account against the cap",
    )
    p.add_argument(
        "--no-extract",
        dest="extract",
        action="store_false",
        help="do not lift <task>.lean out of each result tarball",
    )
    p.add_argument(
        "--retry-failed",
        action="store_true",
        help="RESUBMIT tasks recorded as FAILED/CANCELED or missing a download "
        "-- this pays for the proof again; use --redownload when the proof "
        "already succeeded and only the fetch failed",
    )
    p.add_argument(
        "--redownload",
        action="store_true",
        help="re-fetch tarballs for tasks that finished but never downloaded, "
        "by recorded project_id; submits nothing and exits. Honours --tasks.",
    )
    p.add_argument("--env-file", type=Path, help="KEY=VALUE file to load first")
    p.add_argument("--dry-run", action="store_true", help="list submissions and exit")
    p.add_argument("--status", action="store_true", help="print state.json and exit")
    p.add_argument(
        "--cancel",
        action="store_true",
        help="cancel this run's in-flight projects server-side and exit "
        "(Ctrl-C does not: it only stops the runner). Honours --tasks.",
    )
    p.add_argument(
        "--yes", action="store_true", help="skip the --cancel confirmation prompt"
    )
    p.add_argument("-v", "--verbose", action="store_true")
    return p.parse_args(argv)


def read_task_filter(spec: str | None) -> list[str] | None:
    if not spec:
        return None
    if spec.startswith("@"):
        text = Path(spec[1:]).read_text(encoding="utf-8")
        return [l.strip() for l in text.splitlines() if l.strip() and not l.startswith("#")]
    return [t.strip() for t in spec.split(",") if t.strip()]


class _NoLakeFolderFilter(logging.Filter):
    """Drop the SDK's "no .lake folder" warning, once per run instead of per project.

    It is a false positive here: the uploader strips every standard package and
    all oleans, and Aristotle supplies Mathlib itself. Filtered by message so the
    toolchain-mismatch warning on the same logger still comes through.
    """

    _seen = False

    def filter(self, record: logging.LogRecord) -> bool:
        if "no .lake folder" not in record.getMessage():
            return True
        if not _NoLakeFolderFilter._seen:
            _NoLakeFolderFilter._seen = True
            log.info(
                "note: the SDK's missing-.lake warning is expected here and is "
                "suppressed for the remaining projects -- every dependency "
                "these projects have is stripped from the upload anyway"
            )
        return False


def setup_logging(out_dir: Path, verbose: bool) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    fmt = logging.Formatter("%(asctime)s %(levelname)-7s %(message)s", "%H:%M:%S")
    stream = logging.StreamHandler(sys.stdout)
    stream.setFormatter(fmt)
    fileh = logging.FileHandler(out_dir / "run.log", encoding="utf-8")
    fileh.setFormatter(
        logging.Formatter("%(asctime)s %(levelname)-7s %(message)s")
    )
    logging.basicConfig(
        level=logging.DEBUG if verbose else logging.INFO, handlers=[stream, fileh]
    )
    # The SDK logs a progress bar per project, which buries our own output; print a
    # consolidated line instead.
    sdk = logging.getLogger("aristotlelib")
    sdk.setLevel(logging.WARNING)
    sdk.addFilter(_NoLakeFolderFilter())


def verify_lean(state: State, project: Path) -> None:
    """Compile every returned proof, the other half of the harbor verdict.

    Batched into one Lean invocation, one namespace per task, since each process
    pays a full `import Mathlib`. The container grades each file alone, so a name
    collision between two proofs is reported here and not there: re-check a
    flagged task on its own. Errors are attributed to tasks by line range.
    """
    items = [
        (t, Path(r["lean"]))
        for t, r in sorted(state.tasks.items())
        if r.get("lean") and Path(r["lean"]).exists()
    ]
    if not items:
        log.warning("--verify-lean: no extracted .lean files to compile")
        return

    parts, spans, line = ["import Mathlib\n"], [], 2
    for task, path in items:
        body = re.sub(r"(?m)^import .*$", "", path.read_text(encoding="utf-8",
                                                             errors="replace"))
        block = f"\nnamespace V_{task}\n{body.strip(chr(10))}\nend V_{task}\n"
        spans.append((line, line + block.count("\n"), task))
        parts.append(block)
        line += block.count("\n")

    batch = Path(state.path).parent / "verify_batch.lean"
    batch.write_text("".join(parts), encoding="utf-8", newline="\n")
    log.info("compiling %d proofs as %s (%d lines)", len(items), batch.name, line)

    proc = subprocess.run(["lake", "env", "lean", str(batch)], cwd=project,
                          capture_output=True, text=True, encoding="utf-8",
                          errors="replace")
    out = (proc.stdout or "") + (proc.stderr or "")
    (batch.with_suffix(".log")).write_text(out, encoding="utf-8", newline="\n")

    errs: dict[str, list[str]] = {t: [] for t, _ in items}
    for m in re.finditer(rf"{re.escape(batch.name)}:(\d+):\d+: error: (.*)", out):
        ln = int(m.group(1))
        for a, b, task in spans:
            if a <= ln <= b:
                errs[task].append(m.group(2)[:200])
                break
    for task, es in errs.items():
        state.rec(task)["lean_errors"] = es
    state.save()
    log.info("compiled: %d clean, %d with errors",
             sum(1 for e in errs.values() if not e),
             sum(1 for e in errs.values() if e))


def print_status(state: State) -> None:
    by_status: dict[str, list[str]] = {}
    for task, rec in sorted(state.tasks.items()):
        by_status.setdefault(rec.get("status") or "NOT_SUBMITTED", []).append(task)
    for status in sorted(by_status):
        names = by_status[status]
        print(f"{status:22s} {len(names):3d}  {' '.join(names[:6])}"
              + (" ..." if len(names) > 6 else ""))

    judged = {t: r for t, r in state.tasks.items() if r.get("grade_fails") is not None}
    if judged:
        passed = [t for t, r in judged.items() if not r["grade_fails"]]
        failed = {t: r["grade_fails"] for t, r in judged.items() if r["grade_fails"]}
        # The verifier's text checks only; the file still has to compile (--verify-lean).
        print(f"\nverifier text checks passed: {len(passed)}   failed: {len(failed)}")
        reasons: dict[str, int] = {}
        for fs in failed.values():
            for f in fs:
                reasons[f.split(":")[0]] = reasons.get(f.split(":")[0], 0) + 1
        for r, n in sorted(reasons.items(), key=lambda kv: -kv[1]):
            print(f"    {n:3d}  {r}")
        # A COMPLETE the verifier rejects is the case worth eyeballing.
        suspect = [t for t in failed if state.tasks[t].get("status") == "COMPLETE"]
        if suspect:
            print(f"COMPLETE but rejected ({len(suspect)}): {' '.join(sorted(suspect))}")

        checked = {t: r for t, r in judged.items() if r.get("lean_errors") is not None}
        if checked:
            clean = [t for t in passed if not checked.get(t, {}).get("lean_errors")]
            print(f"compiled clean AND text checks passed: {len(clean)}"
                  f"   (of {len(checked)} compiled)")
        else:
            print("not compiled -- pass --verify-lean PROJECT for the other half"
                  " of the verdict")

    work = sorted(
        r["work_sec"] for r in state.tasks.values() if r.get("work_sec") is not None
    )
    if work:
        coarse = sum(
            1 for r in state.tasks.values() if r.get("work_source") == "observed"
        )
        print(
            f"\nagent time over {len(work)} finished task(s): "
            f"{_fmt_dur(sum(work))} total, {_fmt_dur(work[len(work) // 2])} median, "
            f"{_fmt_dur(work[0])} fastest, {_fmt_dur(work[-1])} slowest"
        )
        queue = [
            r["queue_sec"] for r in state.tasks.values() if r.get("queue_sec")
        ]
        if queue:
            print(
                f"queue time (excluded from the above): {_fmt_dur(sum(queue))} total, "
                f"{_fmt_dur(sorted(queue)[len(queue) // 2])} median"
            )
        if coarse:
            print(
                f"note: {coarse} of these came from polled transitions, not "
                f"events, so they are accurate only to one poll interval"
            )

    # Aristotle's own per-step accounting, reported separately from the span.
    ev = [
        r for r in state.tasks.values() if r.get("event_work_sec") is not None
    ]
    if ev:
        total = sum(r["event_work_sec"] for r in ev)
        seen = sum(r.get("event_count") or 0 for r in ev)
        timed = sum(r.get("event_timed_count") or 0 for r in ev)
        print(
            f"summed event durations over {len(ev)} task(s): {_fmt_dur(total)} "
            f"total ({timed}/{seen} events carried a duration)"
        )
        cut = [t for t, r in state.tasks.items() if r.get("events_truncated")]
        if cut:
            print(f"  partial sums (event log truncated): {' '.join(sorted(cut))}")


def _require_api_key() -> None:
    if not os.environ.get("ARISTOTLE_API_KEY"):
        raise SystemExit(
            "ARISTOTLE_API_KEY is not set (export it, or pass --env-file .env)"
        )
    aristotlelib.set_api_key(os.environ["ARISTOTLE_API_KEY"])


async def cancel_run(args: argparse.Namespace, state: State) -> int:
    """Cancel this run's in-flight projects server-side.

    Ctrl-C only stops the runner; the projects keep working and occupying slots.
    This is a separate, explicit mode so that the default on interrupt leaves
    work running to be re-attached.
    """
    wanted = read_task_filter(args.tasks)
    targets = {
        task: rec
        for task, rec in sorted(state.in_flight().items())
        if wanted is None or task in wanted
    }
    if not targets:
        print("nothing in flight to cancel")
        return 0

    print(f"about to cancel {len(targets)} project(s) started by this run:")
    for task, rec in targets.items():
        print(f"  {task:32s} {rec['project_id']}  ({rec.get('status')})")
    print("Compute already spent on them is lost.")

    if not args.yes and sys.stdin.isatty():
        if input("cancel these? [y/N] ").strip().lower() not in ("y", "yes"):
            print("left running")
            return 0

    failed = 0
    for task, rec in targets.items():
        try:
            project = await Project.from_id(rec["project_id"])
            await _cancel(project)
        except AristotleAPIError as exc:
            failed += 1
            log.error("could not cancel %s (%s): %s", task, rec["project_id"], exc)
            continue
        # Record it locally so a later resume does not re-attach; --retry-failed
        # picks CANCELED back up.
        rec["status"] = "CANCELED"
        rec["finished_at"] = _now()
        state.save()
        log.info("canceled %s (%s)", task, rec["project_id"])

    print(f"canceled {len(targets) - failed}/{len(targets)}")
    return 1 if failed else 0


async def redownload(args: argparse.Namespace, state: State) -> int:
    """Re-fetch tarballs for projects that finished but never downloaded.

    A download can fail while the proof succeeded (the API's concurrency cap
    refuses the fetch). The project is complete server-side and its id is in
    state.json, so this is pure retrieval; --retry-failed would resubmit and pay
    for the proof again. Works from state.json alone and honours --tasks.
    """
    wanted = read_task_filter(args.tasks)
    targets = {
        task: rec
        for task, rec in sorted(state.tasks.items())
        if rec.get("status") in HAS_SOLUTION
        and not rec.get("solution")
        and rec.get("project_id")
        and (wanted is None or task in wanted)
    }
    # Distinguish "nothing to do" from "nothing recoverable": a finished task with
    # no project_id cannot be fetched and needs resubmitting.
    orphaned = [
        task
        for task, rec in state.tasks.items()
        if rec.get("status") in HAS_SOLUTION
        and not rec.get("solution")
        and not rec.get("project_id")
        and (wanted is None or task in wanted)
    ]
    if not targets:
        print("nothing to re-download: no finished task is missing its tarball")
        if orphaned:
            print(f"  ({len(orphaned)} finished with no project_id -- not fetchable;")
            print("   those need --retry-failed, which resubmits)")
        return 0

    print(f"re-downloading {len(targets)} tarball(s); nothing is resubmitted:")
    for task, rec in targets.items():
        print(f"  {task:32s} {rec['project_id']}  ({rec.get('status')})")

    solutions = Path(args.out_dir) / "solutions"
    lean_dir = Path(args.out_dir) / "lean"
    solutions.mkdir(parents=True, exist_ok=True)

    failed = 0
    for task, rec in targets.items():
        try:
            project = await Project.from_id(rec["project_id"])
            path = await _download(project, solutions / f"{task}.tar.gz")
        except AristotleAPIError as exc:
            failed += 1
            rec["error"] = f"redownload: {exc}"
            state.save()
            log.error("re-download %s (%s) failed: %s", task, rec["project_id"], exc)
            continue

        rec["solution"] = str(Path(path).resolve())
        rec["error"] = None
        # The same post-processing as the live path, so recovered rows carry grades.
        if args.extract:
            lean = extract_lean(Path(path), lean_dir, task)
            rec["lean"] = str(lean.resolve()) if lean else None
            if lean is None:
                log.warning("%s: no %s.lean in the result tarball", task, task)
            else:
                fails = _grade(lean, Path(args.projects_dir) / task, task)
                rec["grade_fails"] = fails
                rec["has_sorry"] = any(f.startswith("sorry/admit") for f in fails)
                if fails and rec.get("status") == "COMPLETE":
                    log.warning(
                        "%s: status COMPLETE but %s.lean fails the verifier (%s) "
                        "-- treat as unproved",
                        task,
                        task,
                        "; ".join(fails),
                    )
        state.save()
        log.info("re-downloaded %s (%s)", task, rec["project_id"])

    print(f"re-downloaded {len(targets) - failed}/{len(targets)}")
    return 1 if failed else 0


async def amain(args: argparse.Namespace) -> int:
    state = State.load_or_new(
        Path(args.out_dir) / "state.json", args.prompt, args.projects_dir
    )

    if args.verify_lean:
        if not (args.verify_lean / "lakefile.toml").exists():
            raise SystemExit(f"--verify-lean: not a Lake project: {args.verify_lean}")
        verify_lean(state, args.verify_lean)
        print_status(state)
        return 0

    if args.status:
        print_status(state)
        return 0

    # --cancel works from state.json alone, so it must not require the project tree.
    if args.cancel:
        _require_api_key()
        return await cancel_run(args, state)

    # Also state-only, hence ahead of the projects_dir check; only --extract's
    # grading step needs the project tree.
    if args.redownload:
        if args.extract and not args.projects_dir.is_dir():
            raise SystemExit(
                f"--projects-dir not found: {args.projects_dir} "
                "(needed to grade extracted files; pass --no-extract to skip)"
            )
        _require_api_key()
        return await redownload(args, state)

    if not args.projects_dir.is_dir():
        raise SystemExit(f"--projects-dir not found: {args.projects_dir}")

    if args.retry_failed:
        for task, rec in state.tasks.items():
            if rec.get("status") in ("FAILED", "CANCELED") or (
                rec.get("status") in HAS_SOLUTION and not rec.get("solution")
            ):
                rec["_requeue"] = True
                rec["attempts"] = 0
        state.save()

    if not args.dry_run:  # --dry-run touches no endpoint, so it needs no key
        _require_api_key()

    tasks = discover_tasks(args.projects_dir, read_task_filter(args.tasks))
    if not tasks:
        raise SystemExit(f"no Lean projects found in {args.projects_dir}")

    runner = Runner(args, state, tasks)
    if args.limit:
        runner.pending = runner.pending[: args.limit]

    def stop(*_):
        if runner.stopping:  # second Ctrl-C: give up on the graceful path
            raise KeyboardInterrupt
        runner.stopping = True
        log.warning(
            "stopping: no new submissions, draining %d in flight. Ctrl-C again "
            "to exit now. Either way this does NOT cancel them -- they keep "
            "running server-side and keep holding slots; re-run the same "
            "command to re-attach, or --cancel to actually stop them.",
            len(runner.active),
        )

    try:
        signal.signal(signal.SIGINT, stop)
    except ValueError:  # not the main thread
        pass

    try:
        return await runner.run()
    finally:
        state.save()
        log.info("state written to %s", state.path)


def main() -> int:
    args = parse_args()
    if args.env_file:
        load_env_file(args.env_file)
    setup_logging(Path(args.out_dir), args.verbose)
    try:
        return asyncio.run(amain(args))
    except KeyboardInterrupt:
        log.warning("interrupted")
        return 130


if __name__ == "__main__":
    sys.exit(main())
