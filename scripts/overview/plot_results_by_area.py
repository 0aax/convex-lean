r"""Formalized statements per area of convex mathematics: textbook results
proved, and open problems stated, one horizontal bar per area. The left panel
of the two-part introduction figure; the diagram of the formalization process
(convex_eval_fig/formalization_process_perimeter.pdf) is the right panel.

    uv run --with matplotlib python scripts/overview/plot_results_by_area.py

Counts the task directories under tasks/convex-eval-v28-2h/, one per textbook
result, assigning each to an area by its source chapter (TEXTBOOK_AREA below),
and the problems under tasks/open-problems-100/, assigned by hand in
OPEN_PROBLEM_AREA. Writes figures/overview/results_by_area.{pdf,png}. The
canvas is sized for half of the text width; fonts are sized to read at
about 40% of the canvas.

Needs a LaTeX install on PATH (latex, and dvipng for the PNG).
"""

from __future__ import annotations

from collections import Counter
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.colors as mcolors  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
TEXTBOOK = ROOT / "tasks" / "convex-eval-v28-2h"
OPEN = ROOT / "tasks" / "open-problems-100"
OUT = ROOT / "figures" / "overview"

# Areas, in bar order (top first). Key -> tick label.
AREAS = {
    "sets": "Convex sets",
    "functions": "Convex functions",
    "subdifferentials": "Subdifferential calculus",
    "duality": "Sublinearity \\& conjugacy",
    "operators": "Monotone operators",
    "methods": "Optimization methods",
    "geometry": "Convex geometry",
}

LAYOUTS = {
    "textbook_results_by_area": dict(  # legend below the plot, three columns
        canvas=(14, 5.3), plot_area=(3.3, 1.75, 10.5, 3.45),
        legend=dict(loc="upper center", bbox_to_anchor=(0.5, -0.23), ncol=3, columnspacing=2.0)),
    "textbook_results_by_area_legend_right": dict(  # legend in a column to the right
        canvas=(15, 4.8), plot_area=(3.3, 0.95, 6.9, 3.7),
        legend=dict(loc="center left", bbox_to_anchor=(1.03, 0.5), ncol=1, labelspacing=0.5)),
    "textbook_results_by_area_panel": dict(
        canvas=(8.6, 5.4), plot_area=(3.0, 1.9, 5.4, 3.35),
        legend=dict(loc="upper center", bbox_to_anchor=(0.5, -0.22), ncol=2, columnspacing=1.5)),
}

# Textbook results, by the chapter they come from (task-name prefix).
TEXTBOOK_AREA = [
    ("CAMA_", "sets"),           # Hiriart-Urruty & Lemaréchal, CAMA I chapter III
    ("FCA_chap_A", "sets"), ("FCA_chap_B", "functions"), ("FCA_chap_C", "duality"),
    ("FCA_chap_D", "subdifferentials"), ("FCA_chap_E", "duality"),
    ("RW_chap_8", "subdifferentials"), ("RW_chap_9", "subdifferentials"),
    ("RW_chap_11", "duality"), ("RW_chap_12", "operators"),
    ("BC_chap_6", "sets"), ("BC_chap_7", "duality"), ("BC_chap_8", "functions"),
    ("BC_chap_9", "functions"), ("BC_chap_13", "duality"), ("BC_chap_16", "subdifferentials"),
    ("BC_chap_20", "operators"),
    ("Renegar", "methods"), ("bubeck", "methods"), 
    ("Duchi_L2", "duality"), ("Duchi_Q2", "duality"),  # rearrangement and trace inequalities
    ("Duchi_L4", "sets"), ("Duchi_P4", "sets"), ("Duchi_Q1", "sets"),
    ("Duchi_L8", "methods"), ("Duchi_Q5", "geometry"), ("Duchi_Q9", "geometry"),
    ("Duchi_T10", "operators"),  # Ekeland's variational principle
    ("brunn_minkowski", "geometry"), ("prekopa_leindler", "geometry"), ("grunbaum", "geometry"),
]
RATE_TASKS = ("_bound", "methods")  # the convergence-rate tasks, named *_bound*




def textbook_area(task: str) -> str:
    """The area of a textbook task, from its name; fails unless exactly one rule matches."""
    hits = {area for prefix, area in TEXTBOOK_AREA if task.startswith(prefix)}
    if RATE_TASKS[0] in task:
        hits.add(RATE_TASKS[1])
    if len(hits) != 1:
        raise SystemExit(f"{task}: {len(hits)} areas match ({sorted(hits)})")
    return hits.pop()

# Textbook results, by the chapter they come from (task-name prefix).
TEXTBOOK_AREA = [
    ("CAMA_", "sets"),           # Hiriart-Urruty & Lemaréchal, CAMA I chapter III
    ("FCA_chap_A", "sets"), ("FCA_chap_B", "functions"), ("FCA_chap_C", "duality"),
    ("FCA_chap_D", "subdifferentials"), ("FCA_chap_E", "duality"),
    ("RW_chap_8", "subdifferentials"), ("RW_chap_9", "subdifferentials"),
    ("RW_chap_11", "duality"), ("RW_chap_12", "operators"),
    ("BC_chap_6", "sets"), ("BC_chap_7", "duality"), ("BC_chap_8", "functions"),
    ("BC_chap_9", "functions"), ("BC_chap_13", "duality"), ("BC_chap_16", "subdifferentials"),
    ("BC_chap_20", "operators"),
    ("Renegar", "methods"), ("bubeck", "methods"), 
    ("Duchi_L2", "duality"), ("Duchi_Q2", "duality"),  # rearrangement and trace inequalities
    ("Duchi_L4", "sets"), ("Duchi_P4", "sets"), ("Duchi_Q1", "sets"),
    ("Duchi_L8", "methods"), ("Duchi_Q5", "geometry"), ("Duchi_Q9", "geometry"),
    ("Duchi_T10", "operators"),  # Ekeland's variational principle
    ("brunn_minkowski", "geometry"), ("prekopa_leindler", "geometry"), ("grunbaum", "geometry"),
]
RATE_TASKS = ("_bound", "methods")  # the convergence-rate tasks, named *_bound*

OPEN_PROBLEM_AREA = {
    "bang_plank": "geometry", "borsuk": "geometry", "chebyshev_set": "sets", "danzer": "geometry",
    "dimensional_brunn_minkowski": "geometry", "generalized_lax": "geometry",
    "hadwiger_covering": "geometry", "kalai_3d": "geometry", "kls_conjecture": "geometry",
    "kneser_poulsen": "geometry", "log_brunn_minkowski": "geometry", "mahler_general": "geometry",
    "mahler_symmetric": "geometry", "order_six_djl": "sets", "petty_projection": "geometry",
    "polynomial_hirsch": "geometry", "reflexive_fixed_point": "operators", "reinhardt": "geometry",
    "shannon_capacity_c7": "geometry", "sharp_slicing_isotropic_constant": "geometry",
}

# (label, colour) of the two kinds of statement, in stacking order
KINDS = [("Textbook results", "aqua"), ("Open problems", "coral")]
CANVAS = (7.2, 4.85)  # inches; at half the text width this prints as tall as the diagram beside it
PLOT_AREA = (3.0, 0.55, 4.0, 3.73)  # left, bottom, width, height in inches; the axis label sits above
BAR_STEP, BAR_HEIGHT = 0.62, 0.44  # bar spacing and thickness, in axis units
STYLE = {"text.usetex": True, "font.family": "serif", "font.size": 20,
         "axes.titlesize": 20, "axes.labelsize": 21, "xtick.labelsize": 19,
         "ytick.labelsize": 19, "legend.fontsize": 17, "grid.linestyle": "dotted",
         "axes.axisbelow": True, "savefig.facecolor": "white"}


def textbook_area(task: str) -> str:
    """The area of a textbook task, from its name; fails unless exactly one rule matches."""
    hits = {area for prefix, area in TEXTBOOK_AREA if task.startswith(prefix)}
    if RATE_TASKS[0] in task:
        hits.add(RATE_TASKS[1])
    if len(hits) != 1:
        raise SystemExit(f"{task}: {len(hits)} areas match ({sorted(hits)})")
    return hits.pop()

# Sources in stacking order (bottom first), as grouped in the paper's appendix table.
SOURCES = {
    "CAMA": "Hiriart-Urruty \\& Lemar\\'echal (CAMA I)",
    "FCA": "Hiriart-Urruty \\& Lemar\\'echal (FCA)",
    "Duchi": "Duchi (EE364M)",
    "Bubeck": "Bubeck",
    "SAG": "SAG and SAGA papers",
    "Renegar": "Renegar",
    "RW": "Rockafellar \\& Wets",
    "BC": "Bauschke \\& Combettes",
    "Classical": "Classical results",
}
# task-name prefix -> source; a *_bound* task not matched here is Bubeck's.
SOURCE_OF = [
    ("CAMA_", "CAMA"), ("FCA_", "FCA"), ("Duchi_", "Duchi"), ("bubeck", "Bubeck"),
    ("grunbaum", "Bubeck"), ("sag_", "SAG"), ("saga_", "SAG"), ("Renegar", "Renegar"),
    ("RW_", "RW"), ("BC_", "BC"), ("brunn_minkowski", "Classical"), ("prekopa", "Classical"),
]
COLORS = dict(zip(SOURCES, ["aqua", "magenta", "gold", "green", "darkorange", "slateblue",
                            "red", "sienna", "gray"]))
BAR_STEP, BAR_HEIGHT = 0.62, 0.44  # bar spacing and thickness, in axis units
STYLE = {"text.usetex": True, "font.family": "serif", "font.size": 20,
         "axes.titlesize": 20, "axes.labelsize": 21, "xtick.labelsize": 19,
         "ytick.labelsize": 19, "legend.fontsize": 16, "grid.linestyle": "dotted",
         "axes.axisbelow": True, "savefig.facecolor": "white"}


def draw() -> None:
    tasks = sorted(d.name for d in TEXTBOOK.iterdir() if d.is_dir())
    problems = sorted(d.name for d in OPEN.iterdir() if d.is_dir())
    if set(problems) != set(OPEN_PROBLEM_AREA):
        raise SystemExit(f"open problems differ from OPEN_PROBLEM_AREA: "
                         f"{sorted(set(problems) ^ set(OPEN_PROBLEM_AREA))}")
    counts = [Counter(textbook_area(t) for t in tasks), Counter(OPEN_PROBLEM_AREA[p] for p in problems)]
    print(f"{'':18s}{'proved':>8s}{'open':>6s}")
    for area in AREAS:
        print(f"{area:18s}{counts[0][area]:8d}{counts[1][area]:6d}")
    print(f"{'total':18s}{len(tasks):8d}{len(problems):6d}")

    plt.rcParams.update(STYLE)
    fig = plt.figure(figsize=CANVAS)
    (W, H), (l, b, w, h) = CANVAS, PLOT_AREA
    ax = fig.add_axes((l / W, b / H, w / W, h / H))
    y = [-i * BAR_STEP for i in range(len(AREAS))]  # top bar first
    left = [0] * len(AREAS)
    for (label, colour), c in zip(KINDS, counts):
        v = [c[a] for a in AREAS]
        # a zero-width segment would still draw its outline as a stray line
        shown = [i for i, n in enumerate(v) if n]
        ax.barh([y[i] for i in shown], [v[i] for i in shown], left=[left[i] for i in shown],
                height=BAR_HEIGHT, facecolor=mcolors.to_rgba(colour, 0.45),
                edgecolor=colour, linewidth=1.6, zorder=2, label=label)
        left = [a + b for a, b in zip(left, v)]
    longest = max(left)
    ax.set_yticks(y)
    ax.set_yticklabels(AREAS.values())
    ax.set_ylim(y[-1] - BAR_STEP * 0.8, y[0] + BAR_STEP * 0.8)
    ax.set_xlim(0, longest * 1.26)  # room for the key beside the lower bars
    ax.set_xticks(range(0, longest + 1, 20))
    ax.set_xlabel("Number of formalized statements")
    ax.xaxis.set_label_position("top")  # title-like label above, ticks below
    ax.grid(True, axis="x", ls=":", color="0.7", lw=1)
    # the key sits in the empty space beside the shorter lower bars
    ax.legend(loc="lower right", ncol=1, frameon=False, handlelength=1.0, labelspacing=0.3,
              borderaxespad=0.1, fontsize=17)
    OUT.mkdir(parents=True, exist_ok=True)
    for ext in ("pdf", "png"):
        path = OUT / f"results_by_area.{ext}"
        fig.savefig(path, dpi=200, bbox_inches="tight")
        print("wrote", path.relative_to(ROOT))
    plt.close(fig)


if __name__ == "__main__":
    draw()
