r"""Solve rate on convex-eval-v21-15m against mean proof length.

    uv run --with matplotlib python scripts/convex-eval/plot_convex_v21_solve_rate_vs_proof_length.py

One point per condition in POINTS of plot_convex_v21_timeline.py: the share of
the 100 tasks solved within 15 minutes, against the mean length of its accepted
proofs. Proof length is the Lean code the agent added: lines of code (blank
lines and comments excluded, via code_lines() of
plot_convex_aristotle_vs_claude_code.py) over every `.lean` file of the trial's
LeanWorkspace except `Challenge.lean`, minus those of the issued statement
file, plus one for the `sorry` line the proof replaces. Solved trials only,
read from jobs/convex-eval-v21-15m-final/<condition>/.

The longest proofs (over 1,000 lines) port code from repositories the agent
cloned, so for those models the mean sits well above the median; the script
prints both.

Needs a LaTeX install on PATH (latex, and dvipng for the PNG).
"""

from __future__ import annotations

import json
import statistics
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
from matplotlib.lines import Line2D  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from plot_convex_aristotle_vs_claude_code import HALF_CANVAS, HALF_PLOT_AREA, code_lines, fixed_axes, one_per_task, trial_solved  # noqa: E402
from plot_convex_solve_rate_vs_tokens import END_LABEL_SIZE, FINAL_15M, ROOT, save, trials_15m  # noqa: E402
from plot_convex_v21_timeline import ANTHROPIC, OPENAI, POINTS, STYLE  # noqa: E402

# label offset in points (dx, dy, horizontal alignment) per condition
OFFSETS = {
    "sonnet-4-5": (8, 0, "left"),
    "gpt-5-1": (8, -4, "left"),
    "opus-4-6": (8, -6, "left"),  # under Sonnet 4.5's point: no room to its left
    "gpt-5-4": (8, 0, "left"),
    "opus-4-8": (8, 0, "left"),
    "opus-4-8-xhigh": (8, 0, "left"),
    "gpt-5-6-sol": (8, 0, "left"),
    "fable-5-1": (8, 0, "left"),
    "fable-5-1-xhigh": (-8, 0, "right"),
    "gpt-6-astra": (-8, 0, "right"),
    "opus-5-5": (8, 0, "left"),
    "gpt-6-1-sol": (-8, 0, "right"),
}

XMAX = 250
TASKS = ROOT / "tasks" / "convex-eval-v21-15m"
# issued by the task for the comparator, not written by the agent
ISSUED_MODULES = {"Challenge.lean"}



def draw_scatter(xs: dict[str, float], offsets: dict[str, tuple[float, float, str]], *, xmax: float,
                 step: float, tick_label, xlabel: str, title: str, stem: str,
                 partial: frozenset[str] = frozenset(), legend: bool = True) -> None:
    """One point per POINTS condition at (xs[cond], solve rate); conditions in
    `partial` are drawn hollow with an asterisk. `legend` adds the vendor key."""
    fig, ax = fixed_axes(HALF_PLOT_AREA, HALF_CANVAS)
    for model, effort, cond, _, vendor, _ in POINTS:
        arm = trials_15m(cond)
        x = xs[cond]
        y = 100.0 * sum(ok for ok, _ in arm.values()) / len(arm)
        if x > xmax:
            raise SystemExit(f"{cond}: {x:,.0f} is past the axis")
        st = STYLE[vendor]
        hollow = cond in partial
        ax.scatter([x], [y], marker=st["marker"], s=90, zorder=6, linewidths=1.4 if hollow else 0.6,
                   facecolors="white" if hollow else st["color"],
                   edgecolors=st["color"] if hollow else "black")
        dx, dy, ha = offsets[cond]
        ax.annotate(f"{model}, {effort}" + ("$^*$" if hollow else ""), (x, y), textcoords="offset points",
                    xytext=(dx, dy), ha=ha, va="center", fontsize=END_LABEL_SIZE, zorder=5,
                    annotation_clip=False,
                    bbox=dict(boxstyle="square,pad=0.1", facecolor="white", edgecolor="none", alpha=0.85))
        print(f"{model:12} {effort:9} x {x:9,.1f}, solved {y:4.0f}%")

    ticks = [step * k for k in range(int(xmax // step) + 1)]
    ax.set_xlim(0, xmax)
    ax.set_ylim(0, 100)
    ax.set_yticks(range(0, 101, 20))
    ax.set_xticks(ticks)
    ax.set_xticklabels([tick_label(t) for t in ticks])
    ax.set_xlabel(xlabel)
    ax.set_ylabel(r"Solve rate (\%)")
    ax.set_title(title)
    ax.grid(True, ls=":", color="0.7", lw=1)
    if not legend:
        save(fig, stem, tight=False)
        return
    handles = [
        Line2D([], [], ls="", marker="s", ms=9, color=ANTHROPIC, markeredgecolor="black",
               markeredgewidth=0.6, label="Anthropic\n(Claude Code)"),
        Line2D([], [], ls="", marker="^", ms=9, color=OPENAI, markeredgecolor="black",
               markeredgewidth=0.6, label="OpenAI\n(Codex)"),
    ]
    ax.legend(handles=handles, loc="upper right", fontsize=END_LABEL_SIZE, labelspacing=0.9)
    save(fig, stem, tight=False)


def proof_lengths(condition: str) -> list[int]:
    d = FINAL_15M / condition
    out = []
    for task, trial in one_per_task(d, 100).items():
        if not trial_solved(trial):
            continue
        ws = trial / "artifacts" / "app" / "convex-eval" / "LeanWorkspace"
        files = [p for p in ws.rglob("*.lean") if p.name not in ISSUED_MODULES]
        if not (ws / (task + ".lean")).exists():
            raise SystemExit(f"{condition}/{trial.name}: solved, but no proof in {ws}")
        issued = (TASKS / task / "environment" / (task + ".lean")).read_text(encoding="utf-8")
        # +1: the proof replaces the issued file's one `sorry` line
        added = sum(code_lines(p.read_text(encoding="utf-8")) for p in files) - code_lines(issued) + 1
        if added < 1:
            raise SystemExit(f"{condition}/{trial.name}: {added} proof lines; the issued file was cut down")
        out.append(added)
    return out


def draw() -> None:
    xs = {}
    for model, effort, cond, *_ in POINTS:
        lines = proof_lengths(cond)
        xs[cond] = statistics.mean(lines)
        print(f"{model:12} {effort:9} {len(lines):3} proofs, mean {xs[cond]:6.1f}, "
              f"median {statistics.median(lines):5.0f}, max {max(lines)}")
    draw_scatter(xs, OFFSETS, xmax=XMAX, step=50, tick_label=lambda t: f"{t:.0f}",
                 xlabel="Mean proof lines per solve",
                 title="Solve rate over proof length\n(100 textbook subset, 15 min)",
                 stem="convex_v21_solve_rate_vs_proof_length",
                 legend=False)  # the mean-tokens scatter beside it carries the vendor key


if __name__ == "__main__":
    draw()
