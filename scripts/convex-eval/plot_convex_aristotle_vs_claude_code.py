"""Claude Code against Aristotle on the 315 textbook tasks: cumulative solve rate
over agent time, and the distribution of proof length.

    uv run --with matplotlib python scripts/convex-eval/plot_convex_aristotle_vs_claude_code.py

Claude Code (Opus 5.5) is the gated 2-hour run, read from
jobs/convex-eval-v28-2h-final/, one trial per task. Time is `agent_execution.started_at` to
`finished_at` in result.json, which excludes the environment build, agent
install and verifier. A trial is solved when its reward (result.json, or
`verifier/reward.txt`) is 1.

Aristotle is `aristotle-convex-eval-v28-2h-final`, one record per task in
state.json. Time is `work_sec` in state.json (total minus queue). A trial is
solved when `comparator_reward` is 1: the proof Aristotle returned was installed
into the task's own sandbox and graded by the task's grader (pristine-file
restoration, `lake build`, Comparator with nanoda), whose logs are under
verifier/<task>/.

Proof length is lines of Lean code in the submitted proof, blank lines and
comments excluded, over every `.lean` file of the LeanWorkspace (one Aristotle
proof spans helper modules), so it includes the imports, the given definitions
and the statement. Solved trials only.

The script fails unless each arm has exactly one trial per task. Needs a LaTeX
install on PATH (latex, and dvipng for the PNG).
"""

from __future__ import annotations

import datetime as dt
import json
import statistics
import sys
import tarfile
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402


ROOT = Path(__file__).resolve().parents[2]
JOBS = ROOT / "jobs"
OUT = ROOT / "figures" / "convex-eval"
TASKS = ROOT / "tasks" / "convex-eval-v28-2h"
ARISTOTLE_JOBS = JOBS

# In launch order; a later run's trial replaces an earlier one for the same task.
FINAL_2H = JOBS / "convex-eval-v28-2h-final"
ARISTOTLE_RUNS = ["aristotle-convex-eval-v28-2h-final"]

# Proofs whose only text-check failure is a dropped `import Aesop`, which
# `import Mathlib` already provides.

ARISTOTLE, CLAUDE_CODE = "magenta", "aqua"
SERIES = [("Aristotle", ARISTOTLE), ("Opus 5.5", CLAUDE_CODE)]

XLIM = 60  # minutes; the slowest solve of either arm is 53 min
BIN = 50

CANVAS = (4.36, 4.74)  # inches
PLOT_AREA = (0.938, 0.802, 3.22, 3.22)  # left, bottom, width, height in inches
HALF_CANVAS = (6.67, 4.74)  # inches
HALF_BOX = (4.08, 3.22)  # plot box width, height in inches
LABELLED_PLOT_AREA = (0.938, 0.802, *HALF_BOX)  # left, bottom, width, height in inches
HALF_PLOT_AREA = (0.938 + (HALF_CANVAS[0] - 0.938 - 0.2 - HALF_BOX[0]) / 2, 0.802, *HALF_BOX)

plt.rcParams.update({
    "text.usetex": True,
    "font.family": "serif",
    "font.size": 20,
    "axes.titlesize": 21,
    "axes.labelsize": 22,
    "legend.fontsize": 18,
    "lines.linewidth": 2,
})

# task -> (solved, minutes, code lines of the proof)
Trials = dict[str, tuple[bool, float, int]]



# Lean line counting (blank lines and comments excluded)
def nonblank_lines(text: str) -> int:
    return sum(1 for line in text.splitlines() if line.strip())


def strip_comments(src: str) -> str:
    """Remove `--` line comments and nested `/- ... -/` block comments
    (docstrings included), leaving string literals alone."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth:
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
        elif src.startswith("/-", i):
            depth = 1
            i += 2
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(src[i:j + 1])
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def code_lines(text: str) -> int:
    """Lines of Lean code: neither blank nor comment."""
    return nonblank_lines(strip_comments(text))

def trial_dirs(folder: Path) -> list[Path]:
    """The trial directories (<task>__<id>/, each with a config.json) of a run-output folder."""
    out = sorted(p for p in folder.iterdir() if p.is_dir() and "__" in p.name and (p / "config.json").exists())
    if not out:
        raise SystemExit(f"no trials under {folder}")
    return out


def trial_task(trial: Path) -> str:
    return Path(json.loads((trial / "config.json").read_text(encoding="utf-8"))["task"]["path"]).name


def trial_solved(trial: Path) -> bool:
    """Whether the verifier accepted the proof: the reward in result.json, else verifier/reward.txt."""
    result = json.loads((trial / "result.json").read_text(encoding="utf-8"))
    reward = ((result.get("verifier_result") or {}).get("rewards") or {}).get("reward")
    if reward is None:
        f = trial / "verifier" / "reward.txt"
        if not f.exists():
            raise SystemExit(f"{trial}: no reward")
        reward = f.read_text().strip()
    return float(reward) == 1.0


def one_per_task(folder: Path, expected: set[str] | int) -> dict[str, Path]:
    """{task: trial directory} for a run-output folder, failing unless each task has exactly one trial."""
    rows: dict[str, Path] = {}
    for trial in trial_dirs(folder):
        task = trial_task(trial)
        if task in rows:
            raise SystemExit(f"{task} has more than one trial in {folder}")
        rows[task] = trial
    if isinstance(expected, int):
        if len(rows) != expected:
            raise SystemExit(f"{folder}: {len(rows)} tasks, expected {expected}")
    elif set(rows) != expected:
        raise SystemExit(f"{folder}: trials and tasks disagree: missing {sorted(expected - set(rows))}, "
                         f"extra {sorted(set(rows) - expected)}")
    return rows


def _iso(s: str) -> dt.datetime:
    return dt.datetime.fromisoformat(s.replace("Z", "+00:00"))


def claude_code() -> Trials:
    rows: Trials = {}
    expected = {d.name for d in TASKS.iterdir() if d.is_dir()}
    for task, trial in one_per_task(FINAL_2H, expected).items():
        span = json.loads((trial / "result.json").read_text(encoding="utf-8")).get(
            "agent_execution") or {}
        if not span.get("started_at") or not span.get("finished_at"):
            raise SystemExit(f"{trial.name}: no agent execution window")
        minutes = (_iso(span["finished_at"]) - _iso(span["started_at"])).total_seconds() / 60
        ws = trial / "artifacts" / "app" / "convex-eval" / "LeanWorkspace"
        lines = sum(code_lines(p.read_text(encoding="utf-8")) for p in ws.rglob("*.lean"))
        rows[task] = (trial_solved(trial), minutes, lines)
    return rows


def aristotle() -> Trials:
    rows: Trials = {}
    for run in ARISTOTLE_RUNS:
        d = ARISTOTLE_JOBS / run
        for task, rec in json.loads((d / "state.json").read_text(encoding="utf-8"))["tasks"].items():
            if rec.get("work_sec") is None:
                continue
            if rec.get("comparator_reward") is None:
                raise SystemExit(f"{task}: no comparator verdict in {d / 'state.json'}")
            solved = rec["comparator_reward"] == 1.0
            lines = 0
            with tarfile.open(d / "solutions" / f"{task}.tar.gz") as tar:
                for m in tar.getmembers():
                    # under a project folder or at the archive root, depending on the run
                    if m.isfile() and m.name.endswith(".lean") and "/LeanWorkspace/" in "/" + m.name:
                        lines += code_lines(tar.extractfile(m).read().decode("utf-8"))
            rows[task] = (solved, rec["work_sec"] / 60, lines)
    return rows


def collect() -> tuple[dict[str, Trials], list[str]]:
    arms = {"Aristotle": aristotle(), "Opus 5.5": claude_code()}
    common = sorted(arms["Aristotle"])
    issued = {d.name for d in TASKS.iterdir() if d.is_dir()}
    if not set(common) <= issued:
        raise SystemExit(f"Aristotle tasks not issued: {sorted(set(common) - issued)}")
    missing = sorted(set(common) - set(arms["Opus 5.5"]))
    if missing:
        raise SystemExit(f"Claude Code has no trial for {missing}")
    return {k: {t: v[t] for t in common} for k, v in arms.items()}, common


def curve(solved: list[float], total: int) -> tuple[list[float], list[float]]:
    xs, ys = [0.0], [0.0]
    for i, v in enumerate(solved, start=1):
        xs.append(v)
        ys.append(100.0 * i / total)
    xs.append(float(XLIM))
    ys.append(100.0 * len(solved) / total)
    return xs, ys


def fixed_axes(area: tuple[float, float, float, float] = PLOT_AREA,
               canvas: tuple[float, float] = CANVAS):
    """A `canvas` figure with one axes at `area` (inches); save it with tight=False."""
    fig = plt.figure(figsize=canvas)
    (W, H), (l, b, w, h) = canvas, area
    return fig, fig.add_axes((l / W, b / H, w / W, h / H))


def save(fig, stem: str, tight: bool = True) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    for ext in ("png", "pdf"):
        path = OUT / f"{stem}.{ext}"
        fig.savefig(path, bbox_inches="tight" if tight else None, dpi=200)
        print(f"wrote {path.relative_to(ROOT)}")
    plt.close(fig)


def draw_time(arms: dict[str, Trials], total: int) -> None:
    fig, ax = fixed_axes()  # one third of the page width, beside the release-date plot
    for label, colour in SERIES:
        solved = sorted(m for ok, m, _ in arms[label].values() if ok)
        if solved and solved[-1] > XLIM:
            raise SystemExit(f"{label}'s slowest solve ({solved[-1]:.0f} min) is past the axis")
        xs, ys = curve(solved, total)
        final = 100.0 * len(solved) / total
        ax.plot(xs, ys, drawstyle="steps-post", color=colour, zorder=2,
                label=f"{label}, {f'{final:.1f}'.removesuffix('.0')}\\%")  # 99.7, not a rounded 100
        print(f"{label}: {len(solved)}/{total} solved ({final:.1f}%), "
              f"median solve {statistics.median(solved):.1f} min, max {solved[-1]:.1f} min")

    ax.set_xlim(0, XLIM)
    ax.set_ylim(0, 100)
    ax.set_xticks(range(0, XLIM + 1, 15))
    ax.set_yticks(range(0, 101, 20))
    ax.set_xlabel("Agent time per task (min)")
    ax.set_ylabel(r"Cumulative solve rate (\%)")
    ax.set_title("Solve rate over agent time\n(full textbook set, 2 h)")
    ax.grid(True, ls=":", color="0.7", lw=1)
    ax.legend(loc="lower right", fontsize=13, handlelength=1.2)
    save(fig, "convex_solve_rate_vs_time", tight=False)


def draw_hist(arms: dict[str, Trials]) -> None:
    lines = {label: [n for ok, _, n in arms[label].values() if ok] for label, _ in SERIES}
    top = BIN * (max(max(v) for v in lines.values()) // BIN + 1)
    bins = range(0, top + 1, BIN)
    # one third of the page width, beside the other two; the short y label leaves room to
    # slide the box left so the long x label fits on the canvas
    l, bt, w, h = PLOT_AREA
    fig, ax = fixed_axes((l - 0.22, bt, w, h))
    for label, colour in SERIES:
        ax.hist(lines[label], bins=bins, color=colour, alpha=0.45, zorder=2)
        ax.hist(lines[label], bins=bins, histtype="step", color=colour, lw=1.6, zorder=3)
        ax.plot([], [], "s", color=colour, alpha=0.7, label=label)
        print(f"{label}: {len(lines[label])} proofs, code lines median "
              f"{statistics.median(lines[label])}, min {min(lines[label])}, max {max(lines[label])}")
    ax.set_xlim(0, top)
    ax.set_xlabel("Proof length (lines of Lean code)")
    ax.set_ylabel("Tasks")
    ax.set_title("Distribution of proof length\n(full textbook set, 2 h)")
    ax.grid(True, axis="y", ls=":", color="0.7", lw=1)
    ax.legend(loc="upper right", fontsize=14, handlelength=1.2)
    save(fig, "convex_proof_length_hist_aristotle_vs_claude_code", tight=False)


def draw() -> None:
    arms, common = collect()
    draw_time(arms, len(common))
    draw_hist(arms)


if __name__ == "__main__":
    draw()
