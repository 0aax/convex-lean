"""Cumulative distinct lines written over the run: one figure per budget with
a panel per category (Lean, Writeups, Code).

    uv run --with matplotlib --with numpy python scripts/open-problems/profile_plots/plot_lines_per_task.py --budget 100|1000

Each event is placed at its share of the run's observed time; its first-seen
lines accumulate from there. The curve is the mean over the 20 histories of
the budget, so it reads as lines written per task by each point of the run,
and the dotted line marks where it ends: the mean total lines per task. The
panels share the y label but not the y scale, since the categories differ
by two orders of magnitude. Writes figures/open-problems/
open_problems_profile_<budget>.{pdf,png}. Needs a LaTeX install on PATH.
"""
import argparse

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter

from common import CATS, COLORS, load, save

GRID = np.linspace(0, 100, 401)  # percent of the run
CANVAS = (13.6, 3.6)  # inches
PANEL_W, PANEL_H, BOTTOM = 3.45, 2.2, 0.95  # inches
PANEL_X = (1.3, 5.6, 9.9)  # left edge of each panel; the gaps hold the y tick labels
STYLE = {"text.usetex": True, "font.family": "serif", "font.size": 20, "axes.titlesize": 24,
         "axes.labelsize": 22, "legend.fontsize": 18, "lines.linewidth": 2}


def cumulative(budget):
    """Category -> mean cumulative lines per task on GRID, over the budget's 20 histories."""
    trials, by_trial = load()
    hours = {t["trial"]: t["observed_hours"] for t in trials if t["budget"] == budget}
    if len(hours) != 20:
        raise SystemExit(f"budget {budget}: {len(hours)} histories, expected 20")
    total = {c: np.zeros_like(GRID) for c in CATS}
    for trial, h in hours.items():
        for e in by_trial[trial]:
            at = min(100 * e["elapsed_hours"] / h, 100)
            total[e["category"]] += np.where(GRID >= at, e["first_seen_lines"], 0)
    return {c: v / len(hours) for c, v in total.items()}, len(hours)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--budget", type=int, choices=[100, 1000], required=True)
    args = ap.parse_args()
    plt.rcParams.update(STYLE)
    lines, n = cumulative(args.budget)
    plt.rcParams.update(STYLE)
    fig = plt.figure(figsize=CANVAS)
    W, H = CANVAS
    for cat, x in zip(CATS, PANEL_X):
        y = lines[cat]
        final = y[-1]
        half = GRID[np.searchsorted(y, final / 2)]
        print(f"{cat}: {final:,.0f} lines per task over {n} histories, half written by {half:.0f}% of the run")
        ax = fig.add_axes((x / W, BOTTOM / H, PANEL_W / W, PANEL_H / H))
        ax.axhline(final, ls=":", color="0.35", lw=1.6, zorder=1)
        ax.text(99, final, f"{final:,.0f} lines", ha="right", va="bottom", fontsize=16, color="0.35")
        ax.plot(GRID, y, color=COLORS[cat], zorder=3)
        ax.set_xlim(0, 100)
        ax.set_ylim(0, final * 1.18)
        ax.set_xticks(range(0, 101, 25))
        ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:,.0f}"))
        ax.set_xlabel(r"\% used time")
        ax.set_title(f"{cat} generation")
        ax.grid(True, axis="y", ls=":", color="0.7", lw=1)
    fig.supylabel("Total output lines", x=0.02)
    save(fig, f"open_problems_profile_{args.budget}")


if __name__ == "__main__":
    main()
