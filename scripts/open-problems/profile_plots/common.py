"""Shared data loading and style for the open-problem writing-profile plots.

The dataset is 40 Fable 5.1 open-problem histories (20 problems at each of the
$100 and $1,000 budgets). `data/events.jsonl` has one event per literal write
or edit the agent made: its trial, category (Writeups: .md/.tex; Lean: .lean;
Code: other programming languages), elapsed hours on the run's observed clock,
and `first_seen_lines`, the nonblank lines not previously written to that file
in that run. `data/trials.json` gives each history's budget and observed hours.
"""
import json
from collections import defaultdict
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
OUT = HERE.parents[2] / "figures" / "open-problems"

CATS = ("Lean", "Writeups", "Code")  # panel order, matching the paper caption
COLORS = {"Writeups": "coral", "Lean": "aqua", "Code": "green"}
BUDGETS = (100, 1000)
STYLE = {"text.usetex": True, "font.family": "serif", "font.size": 18,
         "axes.titlesize": 18, "axes.labelsize": 18, "xtick.labelsize": 18,
         "ytick.labelsize": 18, "legend.fontsize": 18, "grid.linestyle": "dotted",
         "axes.axisbelow": True, "savefig.facecolor": "white"}


def load():
    """(trials, events by trial): every trial record, and its events in file order."""
    trials = json.loads((DATA / "trials.json").read_text())
    by_trial = defaultdict(list)
    with (DATA / "events.jsonl").open() as f:
        for line in f:
            e = json.loads(line)
            by_trial[e["trial"]].append(e)
    return trials, by_trial


def save(fig, name, exts=("pdf", "png"), dpi=200, **kw):
    OUT.mkdir(parents=True, exist_ok=True)
    for ext in exts:
        path = OUT / f"{name}.{ext}"
        fig.savefig(path, dpi=dpi, **kw)
        print("wrote", path.relative_to(HERE.parents[2]))
    plt.close(fig)
