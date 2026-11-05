# Prove `hadwiger_covering_conjecture`

You are given a Lean theorem and its negation with `sorry` in place of their proofs. Select one version and produce a Lean proof of that theorem.

**Budget.** You have a budget of $1000 for this task.

When you have a complete proof, run `submit pos` or `submit neg` to have it graded. The run continues until a submission is accepted or the budget is fully used.

## Problem statements

**Informal statement.** `/app/open-eval/statement.tex` states the problem in LaTeX.

**Formal statements.** `/app/open-eval/LeanWorkspace/HadwigerCovering_defs.lean` contains the definitions in Lean. The files `/app/open-eval/LeanWorkspace/HadwigerCovering_pos.lean` and `/app/open-eval/LeanWorkspace/HadwigerCovering_neg.lean` contain the Lean theorem and its negative, respectively. They import the definitions file. Fill in exactly one of the two `sorry`s and leave the other untouched; the unproven sibling theorem cannot be used in your proof, since its `sorry` carries the `sorryAx` axiom, which the grader rejects.

## Environment

- Lean v4.28.0 with Mathlib is installed. The Lake package is `/app/open-eval/`, which holds `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, the library root `LeanWorkspace.lean`, and the `LeanWorkspace/` module directory.
- Prebuilt Mathlib oleans are available.
- The sandbox has internet access.
- Check your progress from `/app/open-eval/`:
  - `lake env lean LeanWorkspace/HadwigerCovering_pos.lean`, `lake env lean LeanWorkspace/HadwigerCovering_neg.lean` — builds a single file and reports errors, goal states at each `sorry`, and warnings.
  - `lake build LeanWorkspace` — what the grader runs.

## Scratch work

`/app/scratch/` is the scratch directory. Put everything that is not part of the submission there: prose drafts, failed attempts, notes, calculations, throwaway scripts.

- It sits outside the Lake package, so nothing in it can affect the build.
- **None of it is graded.** A proof that only exists in `/app/scratch/` scores nothing — only Lean code under `/app/open-eval/` is graded.

## Save your work

Whatever is on disk when the run ends is your submission.

- After any non-trivial progress, save it back into the files under `LeanWorkspace/`.
- Leave your scratch work in `/app/scratch/`. It will not be graded.

## Success criteria

1. `lake build LeanWorkspace`, run from `/app/open-eval/`, exits successfully.
2. `LeanWorkspace.lean`, `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` are unchanged, and so are the theorem statement and the given definitions.
3. `#print axioms` on the theorem you prove -- `hadwiger_covering_conjecture_POS` or `hadwiger_covering_conjecture_NEG` -- reports no `sorryAx` and no axiom beyond Lean's own `propext`, `Classical.choice`, and `Quot.sound`.
4. No `native_decide`.
5. Lean comparator accepts the proof.

Judgements about whether the problem is open are not accepted as solutions.