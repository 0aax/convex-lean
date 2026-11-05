r"""Total output tokens per open problem, one bar per problem under each budget.

    uv run --with matplotlib python scripts/open-problems/plot_open_problems_output_tokens.py

Reads the 40 open-problem histories under jobs/open-problems-final/<budget>/
and writes figures/open-problems/open_problems_output_tokens.{pdf,png}: two
panels, the $100 and the $1,000 budget, each with a bar per problem; the
problems are ordered by their $1,000 count, descending, on both panels.

Counts come from Claude Code's own transcripts, not from harbor's
trajectory.json or result.json. The gated agent runs Claude Code in cycles
(the gate re-prompts it with a continue message until the budget is spent),
one transcript per cycle at agent/claude-code.<k>.txt; agent/claude-code.txt
repeats the last cycle and is skipped. A cycle's output tokens are the
`modelUsage` outputTokens of its `result` line, summed over every model but
the Haiku helper calls. That count includes thinking and subagent output (the
`usage` field of the same line leaves subagents out). A cycle killed before it
wrote a `result` line (three of them, all in trials that stopped early and
were resumed) is instead summed per message id from the session logs under
agent/sessions/projects/, taking the assistant messages between the gate
continue messages that bracket the cycle; that count runs a few percent under
modelUsage, since failed or retried requests leave no persisted message. A
problem with two trials under a budget, one that stopped early and its resume,
is the sum of both.

The script fails unless every problem has a history under both budgets.
Needs a LaTeX install on PATH (latex, and dvipng for the PNG).
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.colors as mcolors  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
JOBS = ROOT / "jobs" / "open-problems-final"
OUT = ROOT / "figures" / "open-problems"
BUDGETS = (100, 1000)
ORDER_BY = 1000  # the budget whose counts set the bar order on every panel

# problem folder -> bar label
LABELS = {
    "bang_plank": "Bang plank",
    "borsuk": "Borsuk",
    "chebyshev_set": "Chebyshev set",
    "danzer": "Danzer",
    "dimensional_brunn_minkowski": "Dim.\\ Brunn--Minkowski",
    "generalized_lax": "Generalized Lax",
    "hadwiger_covering": "Hadwiger covering",
    "kalai_3d": "Kalai $3^d$",
    "kls_conjecture": "KLS",
    "kneser_poulsen": "Kneser--Poulsen",
    "log_brunn_minkowski": "log-Brunn--Minkowski",
    "mahler_general": "Mahler (general)",
    "mahler_symmetric": "Mahler (symmetric)",
    "order_six_djl": "Order-six DJL",
    "petty_projection": "Petty projection",
    "polynomial_hirsch": "Polynomial Hirsch",
    "reflexive_fixed_point": "Reflexive fixed point",
    "reinhardt": "Reinhardt",
    "shannon_capacity_c7": "Shannon $\\Theta(C_7)$",
    "sharp_slicing_isotropic_constant": "Sharp slicing",
}

COLOR = "aqua"
FIGSIZE = (10, 7)
STYLE = {"text.usetex": True, "font.family": "serif", "font.size": 18,
         "axes.titlesize": 18, "axes.labelsize": 18, "xtick.labelsize": 13,
         "ytick.labelsize": 18, "legend.fontsize": 18, "grid.linestyle": "dotted",
         "axes.axisbelow": True, "savefig.facecolor": "white"}


def events(path: Path):
    with path.open(encoding="utf-8", errors="replace") as fh:
        for line in fh:
            try:
                d = json.loads(line)
            except ValueError:
                continue
            if isinstance(d, dict):
                yield d


def result_tokens(transcript: Path) -> int | None:
    """Output tokens of one cycle from its `result` line, or None if it has none."""
    usage = None
    for d in events(transcript):
        if d.get("type") == "result":
            usage = d.get("modelUsage")
    if usage is None:
        return None
    return sum(v["outputTokens"] for k, v in usage.items() if "haiku" not in k)


def text_of(content) -> str:
    if isinstance(content, list):
        return " ".join(c.get("text", "") for c in content if isinstance(c, dict))
    return content if isinstance(content, str) else ""


def session_cycle_tokens(trial: Path, n_cycles: int) -> list[int]:
    """Output tokens per cycle from the session logs, by message id.

    Cycle k > 1 starts at the gate continue message that launched it; the last
    n_cycles - 1 such messages in the main session log are this trial's (a
    resumed trial's log also carries its predecessor's). Subagent logs are
    binned by timestamp into the same windows.
    """
    agent = trial / "agent"
    cont = json.loads((trial / "config.json").read_text())["agent"]["kwargs"]["gate_continue_message"]
    projects = agent / "sessions" / "projects"
    logs = sorted(projects.rglob("*.jsonl"))
    main = [p for p in logs if p.parent.parent == projects]
    if len(main) != 1:
        raise SystemExit(f"{trial}: expected one main session log, found {len(main)}")
    starts = [d.get("timestamp") for d in events(main[0])
              if d.get("type") == "user" and cont in text_of(d.get("message", {}).get("content"))]
    starts = starts[len(starts) - (n_cycles - 1):] if n_cycles > 1 else []
    per_message: dict[tuple[int, str], int] = {}
    for log in logs:
        for d in events(log):
            m = d.get("message")
            if d.get("type") != "assistant" or not isinstance(m, dict) or not m.get("usage") \
                    or "haiku" in m.get("model", ""):
                continue
            cycle = sum(1 for s in starts if d.get("timestamp", "") >= s)
            key = (cycle, m["id"])
            per_message[key] = max(per_message.get(key, 0), m["usage"].get("output_tokens") or 0)
    totals = [0] * n_cycles
    for (cycle, _), n in per_message.items():
        totals[cycle] += n
    return totals


def trial_tokens(trial: Path) -> tuple[int, list[int]]:
    """(output tokens of the trial, cycles counted from the session logs, 1-based)."""
    transcripts = sorted((trial / "agent").glob("claude-code.[0-9]*.txt"))
    if not transcripts:
        raise SystemExit(f"{trial}: no cycle transcripts")
    counts = [result_tokens(t) for t in transcripts]
    fallback = [i + 1 for i, c in enumerate(counts) if c is None]
    if fallback:
        from_logs = session_cycle_tokens(trial, len(transcripts))
        counts = [from_logs[i] if c is None else c for i, c in enumerate(counts)]
    return sum(counts), fallback


def load() -> dict[int, dict[str, int]]:
    totals = {b: {p: 0 for p in LABELS} for b in BUDGETS}
    for budget in BUDGETS:
        seen: dict[str, list[str]] = {p: [] for p in LABELS}
        for trial in sorted((JOBS / str(budget)).iterdir()):
            problem = trial.name.split("__")[0]
            if problem not in LABELS:
                raise SystemExit(f"{trial}: unknown problem {problem!r}")
            n, fallback = trial_tokens(trial)
            totals[budget][problem] += n
            seen[problem].append(trial.name)
            note = f"  (cycles {fallback} counted from session logs)" if fallback else ""
            print(f"${budget:<5} {trial.name:45s} {n:>12,}{note}")
        missing = [p for p, t in seen.items() if not t]
        if missing:
            raise SystemExit(f"${budget}: no history for {missing}")
    return totals


def main() -> None:
    totals = load()
    print(f"\n{'problem':36s}" + "".join(f"{'$' + format(b, ','):>14s}" for b in BUDGETS))
    for p in LABELS:
        print(f"{p:36s}" + "".join(f"{totals[b][p]:>14,}" for b in BUDGETS))
    print(f"{'total':36s}" + "".join(f"{sum(totals[b].values()):>14,}" for b in BUDGETS))

    plt.rcParams.update(STYLE)
    fig, axes = plt.subplots(len(BUDGETS), 1, figsize=FIGSIZE, sharex=True)
    order = sorted(LABELS, key=lambda p: -totals[ORDER_BY][p])
    x = list(range(len(order)))
    face = mcolors.to_rgba(COLOR, 0.45)
    for ax, budget in zip(axes, BUDGETS):
        y = [totals[budget][p] / 1e6 for p in order]
        ax.bar(x, y, width=0.7, facecolor=face, edgecolor=COLOR, linewidth=1.6, zorder=2)
        ax.set_title(f"\\${budget:,} budget total output tokens".replace(",", "{,}"))
        ax.set_ylabel("Output tokens (M)")
        ax.set_ylim(bottom=0)
        ax.grid(True, axis="y", ls=":", color="0.7", lw=1)
    axes[-1].set_xlim(-0.6, len(order) - 0.4)
    axes[-1].set_xticks(x)
    axes[-1].set_xticklabels([LABELS[p] for p in order], rotation=45, ha="right", rotation_mode="anchor")
    fig.tight_layout()

    OUT.mkdir(parents=True, exist_ok=True)
    for ext in ("pdf", "png"):
        path = OUT / f"open_problems_output_tokens.{ext}"
        fig.savefig(path, dpi=200, bbox_inches="tight")
        print("wrote", path.relative_to(ROOT))
    plt.close(fig)


if __name__ == "__main__":
    main()
