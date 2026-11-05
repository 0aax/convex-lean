r"""Cumulative solve rate against output tokens per task, for the 15-minute and
the 2-hour textbook runs.

    uv run --with matplotlib python scripts/convex-eval/plot_convex_solve_rate_vs_tokens.py

A point (x, y) reads: if every trial were capped at x output tokens, y% of the
tasks would be solved. Output tokens include thinking and reasoning; input
tokens are left out. Counts are read from the agents' own transcripts rather
than harbor's trajectory.json / result.json, which are wrong for some Claude
Code versions:

  * Claude Code: the `modelUsage` of the last `result` line of
    agent/claude-code.txt, summed over the task model's aliases (Sonnet 4.5
    reports under two); Haiku helper calls are left out. A run killed at the
    time limit writes no `result` line, so the session log under
    agent/sessions/projects/ is summed per message id instead.
  * Codex: the `usage` of the `turn.completed` event of agent/codex.txt, or
    for a killed run the last `token_count` total of its session rollout.

Claude Code 2.1.42 (Opus 4.6) logs each message's usage as of its first
streamed block, so its killed runs have no output count. Four of its 17 solves
are such runs (UNCOUNTED_OK); its line stops at the 13 counted solves and its
legend entry carries an asterisk.

15 minutes: convex-eval-v21-15m, one line per condition in POINTS of
plot_convex_v21_timeline.py, read from
jobs/convex-eval-v21-15m-final/<condition>/ (one trial per task); solved when
the reward is 1. 2 hours: Claude Code (Opus 5.5) on the 315 tasks, read
from jobs/convex-eval-v28-2h-final/; solved when the reward is 1. Aristotle reports no token counts and is left out.

The token axis is logarithmic and ends just past the costliest solve
(AXIS_MARGIN), where every line is flat.

The script fails unless every task has exactly one trial and every solve has a
count apart from UNCOUNTED_OK. Needs a LaTeX install on PATH (latex, and
dvipng for the PNG).
"""

from __future__ import annotations

import json
import math
import statistics
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import matplotlib.colors as mcolors  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from plot_convex_aristotle_vs_claude_code import CLAUDE_CODE, FINAL_2H, JOBS, one_per_task, trial_solved  # noqa: E402
from plot_convex_aristotle_vs_claude_code import HALF_CANVAS, HALF_PLOT_AREA, LABELLED_PLOT_AREA, fixed_axes  # noqa: E402
from plot_convex_aristotle_vs_claude_code import TASKS as TASKS_2H  # noqa: E402
from plot_convex_v21_timeline import ANTHROPIC, OPENAI, POINTS  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "figures" / "convex-eval"
FINAL_15M = JOBS / "convex-eval-v21-15m-final"

# Half the text width with the shared plot box; line labels sit in the right margin.
END_LABEL_SIZE = 11
# Right edge of the token axis as a multiple of the costliest solve (axis_range).
AXIS_MARGIN = 1.15

plt.rcParams.update({
    "text.usetex": True,
    "font.family": "serif",
    "font.size": 20,
    "axes.titlesize": 21,
    "axes.labelsize": 22,
    "legend.fontsize": 18,
    "lines.linewidth": 2,
})

# Claude Code versions whose session log holds start-of-message usage only.
CLAUDE_CODE_BROKEN_LOG = {"2.1.42"}
# Solves known to have no output count: Opus 4.6 runs killed at the 15-minute limit.
UNCOUNTED_OK = {("opus-4-6", t) for t in ("CAMA_chap_3_4_1_3", "FCA_chap_B_1_2_2",
                                          "FCA_chap_C_1_1_4", "FCA_chap_C_2_1_2")}

# task -> (solved, output tokens, or None when the transcripts give no count)
Trials = dict[str, tuple[bool, int | None]]


def _events(path: Path):
    with path.open(encoding="utf-8", errors="replace") as fh:
        for line in fh:
            try:
                d = json.loads(line)
            except ValueError:  # Codex prints a few plain-text warnings first
                continue
            if isinstance(d, dict):
                yield d


def claude_code_tokens(agent: Path) -> int | None:
    usage, version = None, None
    for d in _events(agent / "claude-code.txt"):
        if d.get("type") == "result":
            usage = d.get("modelUsage")
        elif d.get("type") == "system" and d.get("subtype") == "init":
            version = d.get("claude_code_version")
    if usage is not None:
        return sum(v["outputTokens"] for k, v in usage.items() if "haiku" not in k)
    if version in CLAUDE_CODE_BROKEN_LOG:
        return None
    per_message: dict[str, int] = {}
    for log in (agent / "sessions" / "projects").rglob("*.jsonl"):
        for d in _events(log):
            m = d.get("message")
            if d.get("type") == "assistant" and isinstance(m, dict) and m.get("usage") \
                    and "haiku" not in m.get("model", ""):
                n = m["usage"].get("output_tokens") or 0
                per_message[m["id"]] = max(per_message.get(m["id"], 0), n)
    return sum(per_message.values()) if per_message else None


def codex_tokens(agent: Path) -> int | None:
    for d in _events(agent / "codex.txt"):
        if d.get("type") == "turn.completed":
            return d["usage"]["output_tokens"]
    total = None
    for rollout in (agent / "sessions").rglob("rollout-*.jsonl"):
        for d in _events(rollout):
            p = d.get("payload") or {}
            if p.get("type") == "token_count" and p.get("info"):
                total = p["info"]["total_token_usage"]["output_tokens"]
    return total


def tokens(trial: Path) -> int | None:
    agent = trial / "agent"
    if (agent / "claude-code.txt").exists():
        return claude_code_tokens(agent)
    if (agent / "codex.txt").exists():
        return codex_tokens(agent)
    return None


def check_counted(name: str, rows: Trials) -> None:
    bad = sorted(t for t, (ok, n) in rows.items() if ok and n is None and (name, t) not in UNCOUNTED_OK)
    if bad:
        raise SystemExit(f"{name}: solves without an output count: {bad}")


def trials_15m(condition: str) -> Trials:
    d = FINAL_15M / condition
    rows: Trials = {task: (trial_solved(trial), tokens(trial)) for task, trial in one_per_task(d, 100).items()}
    check_counted(condition, rows)
    return rows


def trials_2h() -> Trials:
    expected = {d.name for d in TASKS_2H.iterdir() if d.is_dir()}
    rows: Trials = {task: (trial_solved(trial), tokens(trial))
                    for task, trial in one_per_task(FINAL_2H, expected).items()}
    check_counted("2h", rows)
    return rows


def curve(solved: list[int], total: int, xmax: float) -> tuple[list[float], list[float]]:
    xs, ys = [1.0], [0.0]
    for i, v in enumerate(solved, start=1):
        xs.append(v)
        ys.append(100.0 * i / total)
    xs.append(xmax)
    ys.append(100.0 * len(solved) / total)
    return xs, ys


def pct(v: float) -> str:
    return f"{v:.1f}".removesuffix(".0")


def counted_solves(arm: Trials) -> list[int]:
    return sorted(n for ok, n in arm.values() if ok and n is not None)


def axis_range(arms: list[Trials]) -> tuple[float, float]:
    """From the decade below the cheapest solve to just past the costliest.

    Not rounded to a tick: every line is flat past the costliest solve, so rounding
    up only spent width on plateaus. AXIS_MARGIN keeps the last step visible.
    """
    counts = [n for arm in arms for n in counted_solves(arm)]
    lo, hi = min(counts), max(counts)
    xlo = 10 ** math.floor(math.log10(lo))
    return xlo, AXIS_MARGIN * hi


def style_axes(ax, xlim: tuple[float, float], title: str) -> None:
    ax.set_xscale("log")
    ax.set_xlim(*xlim)
    ax.set_ylim(0, 100)
    ax.set_yticks(range(0, 101, 20))
    ax.set_xlabel("Output tokens per task")
    ax.set_ylabel(r"Cumulative solve rate (\%)")
    ax.set_title(title)
    ax.grid(True, which="major", ls=":", color="0.7", lw=1)


def labelled_axes():
    return fixed_axes(LABELLED_PLOT_AREA, HALF_CANVAS)


def save(fig, stem: str, tight: bool = True) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    for ext in ("png", "pdf"):
        path = OUT / f"{stem}.{ext}"
        fig.savefig(path, bbox_inches="tight" if tight else None, dpi=200)
        print(f"wrote {path.relative_to(ROOT)}")
    plt.close(fig)


def summary(label: str, arm: Trials) -> str:
    solved = counted_solves(arm)
    n_solved = sum(ok for ok, _ in arm.values())
    med = f"median solve {statistics.median(solved):,.0f}, max {solved[-1]:,.0f}" if solved else "no solves"
    uncounted = sum(n is None for _, n in arm.values())
    return (f"{label}: {n_solved}/{len(arm)} solved ({len(solved)} with a count), {med}, "
            f"trials without a count {uncounted}")


def shade(colour: str, deep: str, f: float) -> tuple[float, float, float]:
    """`colour` blended toward white for f < 0, toward `deep` for f > 0, by |f|."""
    rgb = mcolors.to_rgb(colour)
    end = (1.0, 1.0, 1.0) if f < 0 else mcolors.to_rgb(deep)
    return tuple(c + abs(f) * (e - c) for c, e in zip(rgb, end))


# shade() range, oldest release to newest: mostly toward the deep colour, a darker
# hue of the same family, since the base colours are already light.
SHADE_RANGE = (-0.3, 1.0)
DEEP = {"anthropic": "#08306b", "openai": "#8b0000"}  # deep blue, deep red

LABEL_GAP = 4.2  # least vertical spacing of the end labels, in percentage points


def spread(ys: list[float], gap: float) -> list[float]:
    """Label heights near ys (ascending) at least `gap` apart, each cluster centred on its lines."""
    groups = [[y] for y in ys]
    while True:
        # each group's labels sit `gap` apart, centred on the mean of its lines' heights
        placed = [(sum(g) / len(g) - gap * (len(g) - 1) / 2, g) for g in groups]
        for i in range(len(placed) - 1):
            lo, g = placed[i]
            if placed[i + 1][0] < lo + gap * len(g) - 1e-9:
                groups[i:i + 2] = [groups[i] + groups[i + 1]]
                break
        else:
            return [lo + gap * k for lo, g in placed for k in range(len(g))]


def draw_15m() -> None:
    arms = {cond: trials_15m(cond) for *_, cond, _, _, _ in POINTS}
    xlim = axis_range(list(arms.values()))
    by_vendor = {v: [p for p in POINTS if p[4] == v] for v in ("anthropic", "openai")}
    hues = {"anthropic": ANTHROPIC, "openai": OPENAI}
    lines = []
    for vendor, pts in by_vendor.items():
        for i, (model, effort, cond, _, _, _) in enumerate(pts):  # POINTS is in release order
            # the vendor's colour, light for the oldest release to dark for the newest
            lo, hi = SHADE_RANGE
            colour = shade(hues[vendor], DEEP[vendor], lo + (hi - lo) * i / max(len(pts) - 1, 1))
            solved = counted_solves(arms[cond])
            n_solved = sum(ok for ok, _ in arms[cond].values())
            note = "$^*$" if len(solved) < n_solved else ""  # explained in the caption
            xs, ys = curve(solved, len(arms[cond]), xlim[1])
            lines.append((ys[-1], f"{model}, {effort}{note}", xs, ys, colour,
                          "-" if vendor == "anthropic" else "--"))
            print(summary(f"{model}, {effort}", arms[cond]))

    fig, ax = labelled_axes()
    for _, _, xs, ys, colour, ls in lines:
        ax.plot(xs, ys, drawstyle="steps-post", color=colour, ls=ls, zorder=2)
    style_axes(ax, xlim, "Solve rate over output tokens\n(100 textbook subset, 15 min)")
    # each line named at its right end; labels pushed apart where plateaus are close
    lines.sort(key=lambda r: r[0])
    pt_per_pct = LABELLED_PLOT_AREA[3] * 72 / 100  # the y axis spans 0-100 over the plot height
    for (end, label, *_), y in zip(lines, spread([r[0] for r in lines], LABEL_GAP)):
        ax.annotate(label, (xlim[1], end), xytext=(12, (y - end) * pt_per_pct), textcoords="offset points",
                    ha="left", va="center", fontsize=END_LABEL_SIZE, annotation_clip=False,
                    arrowprops=dict(arrowstyle="-", color="0.55", lw=0.7, shrinkA=0, shrinkB=2))
    save(fig, "convex_v21_solve_rate_vs_tokens", tight=False)


def draw_2h() -> None:
    arm = trials_2h()
    xlim = axis_range([arm])
    solved = counted_solves(arm)
    final = 100.0 * len(solved) / len(arm)
    xs, ys = curve(solved, len(arm), xlim[1])
    # half the text width, beside the proof-length histogram
    fig, ax = fixed_axes(HALF_PLOT_AREA, HALF_CANVAS)
    ax.plot(xs, ys, drawstyle="steps-post", color=CLAUDE_CODE, zorder=2,
            label="Claude Code (Opus 5.5)")
    style_axes(ax, xlim, "Solve rate over output tokens\n(full textbook set, 2 h)")
    ax.legend(loc="lower right", fontsize=14, handlelength=2.2)
    print(summary("Claude Code (Opus 5.5), 2h", arm))
    save(fig, "convex_solve_rate_vs_tokens", tight=False)


if __name__ == "__main__":
    draw_15m()
    draw_2h()
