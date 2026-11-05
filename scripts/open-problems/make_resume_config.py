"""Build a harbor job config that resumes a finished trial in a snapshot of its
own sandbox, via the agent's native `claude --resume`.

    uv run python scripts/open-problems/make_resume_config.py <TRIAL_DIR> [options]

Reads from the finished trial jobs/<job>/<trial>: config.json (task, agent,
environment), agent/gate/cycles.jsonl (per-cycle costs), the root session log
under agent/sessions/, and the snapshot name from
configs/open-problems/resume/<trial>/snapshot.json written by
a snapshot of the sandbox (--snapshot NAME); the released resumes used --in-place.

The remaining budget is the original gate cap minus what the CLI reported
spent: the sum of the cycles.jsonl costs, plus the session file's last
`budget_usd.used` reading for a final cycle logged at 0 (a crash leaves no
result record). Override with --spent or --remaining.

Writes configs/open-problems/resume/<trial>/job.json, a prompt_template.md
that renders only the gate's continue message, and a sanitized copy of the
session log for agents[0].load_trajectory, then prints the `harbor run`
command.
"""
import argparse
import json
import re
import sys
import uuid
from pathlib import Path

MIN_REMAINING_DEFAULT = 5.0
SANDBOX_RE = re.compile(r"Keeping Daytona sandbox alive[^:]*:\s*([0-9a-f-]{36})")
INPLACE_IMPORT_PATH = "resume_daytona:ResumeDaytonaEnvironment"


def sandbox_id_from_trial(trial_dir: Path) -> str:
    log = trial_dir / "trial.log"
    if not log.exists():
        sys.exit(f"{log} not found; --in-place needs the sandbox id from trial.log")
    ids = SANDBOX_RE.findall(log.read_text(encoding="utf-8", errors="replace"))
    if not ids:
        sys.exit(f"no 'Keeping Daytona sandbox alive' line in {log}")
    return ids[-1]


def load_json(p: Path):
    return json.loads(p.read_text(encoding="utf-8"))


def find_session_file(trial_dir: Path) -> Path:
    found = []
    for p in (trial_dir / "agent" / "sessions" / "projects").glob("*/*.jsonl"):
        try:
            uuid.UUID(p.stem)
        except ValueError:
            continue
        found.append(p)
    if len(found) != 1:
        sys.exit(f"expected exactly one root session file under {trial_dir / 'agent/sessions/projects'}, found {len(found)}")
    return found[0]


def copy_session_trimmed(src: Path, dst: Path) -> int:
    """Copy src to dst, dropping trailing lines that are not valid JSON. Returns the count dropped."""
    lines = src.read_bytes().split(b"\n")
    if lines and lines[-1] == b"":
        lines.pop()
    bad = 0
    while lines:
        try:
            json.loads(lines[-1])
            break
        except Exception:
            lines.pop()
            bad += 1
    dst.write_bytes(b"\n".join(lines) + (b"\n" if lines else b""))
    return bad


def last_budget_meter(session: Path):
    """Last `budget_usd` attachment in the session file: (used, total, timestamp) or None."""
    last = None
    with session.open("rb") as f:
        for raw in f:
            if b'"budget_usd"' not in raw:
                continue
            try:
                d = json.loads(raw)
            except Exception:
                continue
            att = d.get("attachment") or {}
            if att.get("type") == "budget_usd":
                last = (float(att.get("used", 0.0)), float(att.get("total", 0.0)), d.get("timestamp"))
    return last


def read_cycles(trial_dir: Path):
    p = trial_dir / "agent" / "gate" / "cycles.jsonl"
    if not p.exists():
        return []
    rows = []
    for line in p.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line:
            rows.append(json.loads(line))
    return rows


def compute_spent(trial_dir: Path, session: Path, cap: float | None = None):
    """CLI-accounting spend with a printed breakdown. Returns (spent, elapsed_sec)."""
    rows = read_cycles(trial_dir)
    streams = sorted((trial_dir / "agent").glob("claude-code.*.txt"))
    logged = sum(float(r.get("invocation_cost_usd") or 0.0) for r in rows)
    elapsed = float(rows[-1].get("elapsed_sec") or 0.0) if rows else 0.0
    print("cycles.jsonl:")
    for r in rows:
        print(f"  cycle {r.get('cycle')}: ${float(r.get('invocation_cost_usd') or 0):.2f}  stop={r.get('stop')}")
    unlogged = False
    if rows and float(rows[-1].get("invocation_cost_usd") or 0.0) == 0.0:
        unlogged = True
        print("  last logged cycle has cost 0 (no result record): using the CLI budget meter for it")
    if len(streams) > len(rows):
        unlogged = True
        print(f"  {len(streams)} stream snapshots but {len(rows)} logged cycles: the final cycle was never logged")
    if not rows:
        unlogged = True
        print("  no cycles.jsonl: using the CLI budget meter for the whole trial")
    meter = last_budget_meter(session)
    # A meter whose `total` equals cap minus the logged spend belongs to a cycle
    # that was never logged (a crash or a stall).
    if meter is not None and cap is not None and abs(meter[1] - (cap - logged)) < 0.05:
        if not unlogged:
            print("  budget meter total equals cap - logged: the final cycle was never logged")
        unlogged = True
    meter_used = 0.0
    if unlogged:
        if meter is None:
            print("  WARNING: no budget_usd meter reading found; the unlogged cycle counts as $0")
        else:
            meter_used = meter[0]
            print(f"  budget meter: used ${meter[0]:.2f} of ${meter[1]:.2f} at {meter[2]}")
    spent = logged + meter_used
    print(f"spent (CLI accounting): ${logged:.2f} logged + ${meter_used:.2f} meter = ${spent:.2f}")
    return spent, elapsed


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("trial_dir", help="jobs/<job>/<trial> of the finished trial")
    ap.add_argument("--in-place", action="store_true",
                    help="resume in the ORIGINAL sandbox (faithful disk) via resume_daytona env, "
                         "instead of a fresh sandbox from a snapshot")
    ap.add_argument("--snapshot", help="Daytona snapshot name (default: from <out>/snapshot.json); "
                    "ignored with --in-place")
    ap.add_argument("--out-root", default="configs/open-problems/resume", help="output root; files go in <out-root>/<trial>/")
    ap.add_argument("--job-name", help="harbor job name (default resume-<trial>)")
    ap.add_argument("--spent", type=float, help="override the computed spend (USD)")
    ap.add_argument("--remaining", type=float, help="override the remaining budget (USD)")
    ap.add_argument("--min-remaining", type=float, default=MIN_REMAINING_DEFAULT,
                    help=f"refuse if remaining is below this (default {MIN_REMAINING_DEFAULT})")
    ap.add_argument("--no-time-adjust", action="store_true",
                    help="keep gate_time_limit_sec as in the source instead of subtracting elapsed time")
    ap.add_argument("--force", action="store_true", help="write the config even if remaining is below the floor")
    a = ap.parse_args()

    trial_dir = Path(a.trial_dir)
    cfg = load_json(trial_dir / "config.json")
    trial_name = cfg.get("trial_name") or trial_dir.name
    out_dir = Path(a.out_root) / trial_name
    out_dir.mkdir(parents=True, exist_ok=True)

    snapshot = None
    sandbox_id = None
    if a.in_place:
        sandbox_id = sandbox_id_from_trial(trial_dir)
        print(f"in-place resume: original sandbox {sandbox_id}")
    else:
        snapshot = a.snapshot
        if not snapshot:
            sj = out_dir / "snapshot.json"
            if not sj.exists():
                sys.exit(f"no --snapshot given and {sj} not found; pass --snapshot NAME or use --in-place")
            snapshot = load_json(sj)["snapshot"]

    agent = cfg["agent"]
    kwargs = dict(agent.get("kwargs") or {})
    task_path = cfg["task"]["path"]
    cap = float(kwargs.get("gate_cap_usd") or kwargs.get("max_budget_usd") or 0.0)
    if cap <= 0:
        sys.exit("source config has no gate_cap_usd/max_budget_usd to compute a remainder from")

    session_src = find_session_file(trial_dir)
    session_dst = out_dir / session_src.name
    dropped = copy_session_trimmed(session_src, session_dst)
    print(f"session: {session_src.name} ({session_src.stat().st_size} bytes), trailing lines dropped: {dropped}")

    spent, elapsed = compute_spent(trial_dir, session_src, cap)
    if a.spent is not None:
        spent = a.spent
        print(f"spent overridden: ${spent:.2f}")
    remaining = round(cap - spent, 2) if a.remaining is None else a.remaining
    print(f"cap ${cap:.2f} -> remaining ${remaining:.2f}")
    if remaining < a.min_remaining and not a.force:
        sys.exit(f"remaining ${remaining:.2f} is below the floor ${a.min_remaining:.2f}; pass --force to proceed anyway")

    continue_msg = kwargs.get("gate_continue_message")
    if not continue_msg:
        sys.exit("source config has no gate_continue_message; the resume turn needs it")
    template = out_dir / "prompt_template.md"
    # harbor's renderer requires the template to reference `instruction`; a no-op
    # `set` satisfies it so the rendered prompt is only the continue message.
    template.write_text(
        "{#- resume turn: the task instruction is intentionally not re-sent -#}\n"
        "{%- set _unused = instruction -%}\n" + continue_msg.rstrip() + "\n",
        encoding="utf-8",
    )

    time_limit = kwargs.get("gate_time_limit_sec")
    if time_limit is not None and not a.no_time_adjust:
        left = max(3600.0, float(time_limit) - elapsed)
        print(f"gate_time_limit_sec: {float(time_limit):.0f} - {elapsed:.0f} elapsed -> {left:.0f}")
        time_limit = str(int(left))

    posix = lambda p: Path(p).as_posix()
    new_kwargs = dict(kwargs)
    new_kwargs["max_budget_usd"] = f"{remaining:.2f}"
    new_kwargs["gate_cap_usd"] = f"{remaining:.2f}"
    new_kwargs["prompt_template_path"] = posix(template)
    if time_limit is not None:
        new_kwargs["gate_time_limit_sec"] = time_limit

    env_cfg = dict(cfg.get("environment") or {})
    env_kwargs = dict(env_cfg.get("kwargs") or {})
    if a.in_place:
        # In-place resume: attach to the original sandbox. Run harbor with
        # PYTHONPATH=environments so environments/resume_daytona.py is importable.
        env_cfg.pop("type", None)
        env_kwargs.pop("snapshot_template_name", None)
        env_cfg["import_path"] = INPLACE_IMPORT_PATH
        env_kwargs["resume_sandbox_id"] = sandbox_id
    else:
        env_kwargs["snapshot_template_name"] = snapshot
    env_cfg["kwargs"] = env_kwargs

    job_name = a.job_name or f"resume-{re.sub(r'[^A-Za-z0-9_.-]+', '-', trial_name)}"
    job = {
        "job_name": job_name,
        "n_concurrent_trials": 1,
        "n_attempts": 1,
        "environment": env_cfg,
        "agents": [
            {
                "import_path": agent["import_path"],
                "model_name": agent.get("model_name"),
                "env": agent.get("env") or {},
                "load_trajectory": posix(session_dst),
                "kwargs": new_kwargs,
            }
        ],
        "tasks": [{"path": task_path}],
        "resume_of": {
            "trial_dir": posix(trial_dir),
            "trial_name": trial_name,
            "mode": "in-place" if a.in_place else "snapshot",
            "snapshot": snapshot,
            "sandbox_id": sandbox_id,
            "cap_usd": cap,
            "spent_usd": round(spent, 2),
            "remaining_usd": remaining,
        },
    }
    if cfg.get("environment_build_timeout_multiplier") is not None:
        job["environment_build_timeout_multiplier"] = cfg["environment_build_timeout_multiplier"]

    out = out_dir / "job.json"
    out.write_text(json.dumps(job, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out}")
    print(f"wrote {template}")
    print()
    print("run from the repo root on the machine that will host the orchestrator:")
    print(f"  PYTHONUTF8=1 uv run harbor run -c {posix(out)} --env-file .env")


if __name__ == "__main__":
    main()
