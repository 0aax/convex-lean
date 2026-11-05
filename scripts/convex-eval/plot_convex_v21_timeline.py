r"""Solve rate on convex-eval-v21-15m against model release date.

    uv run --with matplotlib python scripts/convex-eval/plot_convex_v21_timeline.py

One point per condition in POINTS: the share of the 100 Lean v4.21 tasks a
model solved within the 15-minute limit, in its own CLI (Claude Code for
Anthropic, Codex for OpenAI), read from
jobs/convex-eval-v21-15m-final/<condition>/ (one trial per task); solved when
the reward is 1. Each point
is labelled "model, effort". Each vendor's models are joined over time by a
dash-dot line. Opus 4.8 and Fable 5.1 are shown at xhigh effort. Sonnet 4.5
has no effort setting and ran with a fixed 32k-token thinking budget per
response.

Sized for one third of the page width, on the same canvas and plot box as
convex_solve_rate_vs_time and the proof-length histogram. Needs a LaTeX install
on PATH (latex, and dvipng for the PNG).
"""

from __future__ import annotations

import datetime as dt
import json
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.dates as mdates  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patheffects import withStroke  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
FINAL_15M = ROOT / "jobs" / "convex-eval-v21-15m-final"
sys.path.insert(0, str(Path(__file__).resolve().parent))
from plot_convex_aristotle_vs_claude_code import fixed_axes, one_per_task, trial_solved  # noqa: E402
OUT = ROOT / "figures" / "convex-eval"

ANTHROPIC, OPENAI = "aqua", "coral"
# (model, effort, condition folder, release date, vendor, label offset in
#  points and horizontal alignment)
POINTS = [
    ("Sonnet 4.5", "thinking", "sonnet-4-5", dt.date(2025, 9, 29), "anthropic", (-8, 14, "left")),
    ("GPT-5.1", "high", "gpt-5-1", dt.date(2025, 11, 13), "openai", (0, -16, "center")),
    ("Opus 4.6", "max", "opus-4-6", dt.date(2026, 2, 5), "anthropic", (12, 0, "left")),
    ("GPT-5.4", "xhigh", "gpt-5-4", dt.date(2026, 3, 5), "openai", (-12, 6, "right")),
    ("Opus 4.8", "xhigh", "opus-4-8-xhigh", dt.date(2026, 5, 28), "anthropic", (12, 0, "left")),
    ("GPT-5.6 Sol", "max", "gpt-5-6-sol", dt.date(2026, 7, 9), "openai", (-14, 0, "right")),
    ("Fable 5.1", "xhigh", "fable-5-1-xhigh", dt.date(2026, 9, 1), "anthropic", (-10, -14, "right")),
    ("GPT-6 Astra", "max", "gpt-6-astra", dt.date(2026, 9, 3), "openai", (0, 14, "center")),
    ("Opus 5.5", "max", "opus-5-5", dt.date(2026, 9, 22), "anthropic", (-12, 0, "right")),
    ("GPT-6.1 Sol", "max", "gpt-6-1-sol", dt.date(2026, 9, 29), "openai", (-12, -4, "right")),
]
LABEL_PT = 11  # point labels and legend
STYLE = {"anthropic": dict(color=ANTHROPIC, marker="s"), "openai": dict(color=OPENAI, marker="^")}

plt.rcParams.update({
    "text.usetex": True,
    "font.family": "serif",
    "font.size": 20,
    "axes.titlesize": 21,
    "axes.labelsize": 22,
    "legend.fontsize": 18,
    "lines.linewidth": 2,
})


def scores() -> dict[str, float]:
    """condition -> solve rate in percent; every condition must have all 100 tasks graded."""
    out = {}
    for cond in {cond for _, _, cond, _, _, _ in POINTS}:
        trials = one_per_task(FINAL_15M / cond, 100)
        out[cond] = 100.0 * sum(trial_solved(t) for t in trials.values()) / len(trials)
    return out


def draw() -> None:
    rate = scores()
    fig, ax = fixed_axes()  # one third of the page width
    # each vendor's models joined over time (dash-dot)
    for vendor, st in STYLE.items():
        line = sorted((day, rate[cond]) for _, _, cond, day, v, _ in POINTS if v == vendor)
        ax.plot([p[0] for p in line], [p[1] for p in line], ls="-.", lw=1.5, color=st["color"], zorder=2)
    for model, effort, cond, day, vendor, (dx, dy, ha) in POINTS:
        st = STYLE[vendor]
        y = rate[cond]
        ax.scatter([day], [y], marker=st["marker"], s=130, color=st["color"],
                   edgecolors="black", linewidths=0.6, zorder=6)  # above the labels
        ax.annotate(f"{model}, {effort}", (day, y), textcoords="offset points", xytext=(dx, dy),
                    ha=ha, va="center", fontsize=LABEL_PT, zorder=5,
                    # white outline keeps labels legible where a line passes under them
                    path_effects=[withStroke(linewidth=3, foreground="white")])
        print(f"{model:12} {effort:13} {day}  {y:5.1f}%")

    ax.set_ylim(0, 100)
    ax.set_yticks(range(0, 101, 20))
    # room either side of the first and last release for their labels
    ax.set_xlim(dt.date(2025, 8, 5), dt.date(2027, 2, 1))
    # labelled ticks every six months, minor ticks quarterly; the axis runs on past the
    # last release so its labels fit
    ax.set_xticks([dt.date(2025, 10, 1), dt.date(2026, 4, 1), dt.date(2026, 10, 1)])
    ax.set_xticks([dt.date(2026, 1, 1), dt.date(2026, 7, 1)], minor=True)
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b '%y", usetex=False))  # short form: the axis is narrow
    ax.set_xlabel("Model release date")
    ax.set_ylabel(r"Solve rate (\%)")
    ax.set_title("Solve rate over release date\n(100 textbook subset, 15 min)")
    ax.grid(True, ls=":", color="0.7", lw=1)
    handles = [
        Line2D([], [], ls="", marker="s", ms=11, color=ANTHROPIC, markeredgecolor="black",
               markeredgewidth=0.6, label="Anthropic"),
        Line2D([], [], ls="", marker="^", ms=11, color=OPENAI, markeredgecolor="black",
               markeredgewidth=0.6, label="OpenAI"),
    ]
    ax.legend(handles=handles, loc="upper left", fontsize=LABEL_PT, handlelength=0.7,
              handletextpad=0.3, borderpad=0.2, borderaxespad=0.25, labelspacing=0.35)

    OUT.mkdir(parents=True, exist_ok=True)
    for ext in ("png", "pdf"):
        path = OUT / f"convex_v21_success_rate_vs_release_date.{ext}"
        fig.savefig(path, dpi=200)  # no tight bbox: the canvas is fixed
        print(f"wrote {path.relative_to(ROOT)}")
    plt.close(fig)


if __name__ == "__main__":
    draw()
