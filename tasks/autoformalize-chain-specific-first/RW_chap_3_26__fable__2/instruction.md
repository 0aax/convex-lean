# Formalize Theorem 3.26 (Rockafellar & Wets, Variational Analysis)

Write a Lean 4 statement of **Theorem 3.26** from Rockafellar & Wets, *Variational Analysis*, Chapter 3, Theorem 3.26 (horizon functions and coercivity) — PDF page 102 of `/app/corpus/variational_analysis.pdf`.

Put it in `/app/autoformalize/LeanWorkspace/RW_chap_3_26.lean`, the file should have a theorem named `RW_chap_3_26` whose proof is `sorry`. Do not prove it. The project keeps its definitions in `/app/autoformalize/LeanWorkspace/Defs.lean`.

Formalize this at a suitable level of generality. Your statement will become part of a project that formalizes results from every source in the corpus.

The project already contains formalizations of other results in the corpus. You may edit them, but the package must still build.

**Time.** 30 minutes. Whatever is on disk at the end is your submission.

## Environment

- `/app/corpus/` holds the books and papers as PDFs (titles in `/app/corpus/INDEX.md`).
- The Lake package is `/app/autoformalize/` (Lean v4.28.0, Mathlib prebuilt). Check your file with `lake env lean LeanWorkspace/RW_chap_3_26.lean` or `lake build LeanWorkspace` from there.
- Web access is permitted.
- `/app/scratch/` is for notes and extracted text; it is not assessed.

## Format (checked by `submit` and the grader)

We will check that `lake build LeanWorkspace` succeeds and the file has a single theorem `RW_chap_3_26` whose proof is `sorry`.
