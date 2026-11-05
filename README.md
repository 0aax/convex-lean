# convex-lean

Evaluating agents on proving the mathematics of convexity in Lean 4.

## Setup

Install the pinned environment:

```
uv sync --frozen
```

Put API keys and other variables in a `.env` file at the repo root: `ANTHROPIC_API_KEY` and `OPENAI_API_KEY` for the agents, `DAYTONA_API_KEY` for the sandboxes, `ARISTOTLE_API_KEY` for Aristotle, and `CLAUDE_CODE_MAX_OUTPUT_TOKENS=128000`

The configs run each trial in a Daytona sandbox.

## Run

Each experiment is one Harbor run config. For example, to run the 2h textbook evaluation:

```
PYTHONUTF8=1 uv run harbor run -c configs/convex-eval/run-convex-eval-v28-2h.json --env-file .env
```

The configs are:
  - Textbook, 15 minutes: `configs/convex-eval/run-convex-eval-v21-15m-<model>.json`
  - Textbook, 2 hours: `configs/convex-eval/run-convex-eval-v28-2h.json`
  - Open problems, $100 or $1,000 budget: `configs/open-problems/run-open-problems-{100,1000}.json`

To evaluate Aristotle on the 2 hour textbook tasks:
```
uv run --no-project --with aristotlelib==2.1.0 python -s scripts/convex-eval/aristotle/run_aristotle.py \
    --projects-dir aristotle/projects --out-dir jobs/aristotle-convex-eval-v28-2h --max-active 1
```

To run the autoformalization examples, there are two stages. Stage 1 runs all three models on the three *Fundamentals of Convex Analysis* results (`configs/autoformalize/run-autoformalize-chain-stage1*.json`, one config per prompt and attempt). Stage 2 runs one config per model, prompt, and attempt (`configs/autoformalize/run-autoformalize-chain-specific-first*.json`) on tasks that carry that model's stage-1 files.

Note: The tasks copy a corpus of source PDFs into their environment. Those books and papers are not redistributed here, please obtain them and place them under `textbooks/` with the relative paths listed in any task's `environment/INDEX.md`, and run `uv run python scripts/autoformalize/install_corpus.py` to copy them into every task.

## Run outputs

Extract the runs into the `jobs` directory. Each trial directory contains the instruction and config, the agent transcript and session logs, the verifier logs and reward, and the sandbox files under `artifacts/`.
- All runs can be downloaded at this [link](https://drive.google.com/file/d/1sk0KR3_HN-GEaL1tqh6KL-KV4o_in2_g/view?usp=sharing).

| folder | contents |
| --- | --- |
| `jobs/convex-eval-v21-15m-final/<condition>/` | 100 textbook tasks, 15 minutes. |
| `jobs/convex-eval-v28-2h-final/` | all textbook tasks, 2 hours. |
| `jobs/aristotle-convex-eval-v28-2h-final/` | all textbook tasks, Aristotle. |
| `jobs/open-problems-final/<budget>/` | open problems, a problem with two trials under a budget is one that stopped early and was resumed. |
| `jobs/autoformalization/<prompt>/` | autoformalization examples under the basic and detailed prompts: `stage1/attempt-<k>/` holds the first formalizations and `stage2/` the second ones. |

## Analysis

`analysis/` holds the paper's manual analyses of the run outputs.

- `convex-eval-v28-2h-textbook-references.json`: agent named the source textbook in its own text (messages, reasoning and tool-call arguments, not the prompt or tool output).
- `convex-eval-v28-2h-python-use.json`: agent used Python for numerical or symbolic computation.
- `open-problems-lean-statement-checks.json`: evidence from open-problem history showing that the agent checked the Lean statement matches the conjecture.
- `open-problems-budget-related-decisions.json`: for each $100 open-problem history, evidence showing the agent weighed its remaining budget in choosing what to do next.