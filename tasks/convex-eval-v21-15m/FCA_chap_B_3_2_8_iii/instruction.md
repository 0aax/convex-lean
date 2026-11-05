# Prove `FCA_chap_B_3_2_8_iii`

You are given a Lean theorem with `sorry` in place of its proof. Produce a Lean proof of that theorem.

When you have a complete proof, run `submit` to have it graded.

## Problem statement

`/app/convex-eval/LeanWorkspace/FCA_chap_B_3_2_8_iii.lean` contains the definitions the statement depends on, followed by the theorem `FCA_chap_B_3_2_8_iii`.

## Environment

- Lean v4.21.0 with Mathlib is installed. The Lake package is `/app/convex-eval/`, which holds `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, the library root `LeanWorkspace.lean`, and the `LeanWorkspace/` module directory.
- Prebuilt Mathlib oleans are available.
- The sandbox has internet access.
- Check your progress from `/app/convex-eval/`:
  - `lake env lean LeanWorkspace/FCA_chap_B_3_2_8_iii.lean` — builds a single file and reports errors, goal states at each `sorry`, and warnings.
  - `lake build LeanWorkspace` — what the grader runs.

## Scratch work

`/app/scratch/` is the scratch directory. Put everything that is not part of the submission there: prose drafts, failed attempts, notes, calculations, throwaway scripts.

- It sits outside the Lake package, so nothing in it can affect the build.
- **None of it is graded.** A proof that only exists in `/app/scratch/` scores nothing — only Lean code under `/app/convex-eval/` is graded.

## Save your work

Whatever is on disk when the run ends is your submission.

- After any non-trivial progress, save it back into the files under `LeanWorkspace/`.
- Leave your scratch work in `/app/scratch/`. It will not be graded.

## Success criteria

1. `lake build LeanWorkspace`, run from `/app/convex-eval/`, exits successfully.
2. `LeanWorkspace.lean`, `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` are unchanged, and so are the theorem statement and the given definitions.
3. `#print axioms` on the theorem you prove -- `FCA_chap_B_3_2_8_iii` -- reports no `sorryAx` and no axiom beyond Lean's own `propext`, `Classical.choice`, and `Quot.sound`.
4. No `native_decide`.
5. Lean comparator accepts the proof.
