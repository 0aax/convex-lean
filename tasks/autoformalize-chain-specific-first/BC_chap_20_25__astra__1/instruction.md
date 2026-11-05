# Formalize Theorem 20.25 (Bauschke & Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces)

Write a Lean 4 statement of **Theorem 20.25** from Bauschke & Combettes, *Convex Analysis and Monotone Operator Theory in Hilbert Spaces*, Chapter 20, Theorem 20.25 (Moreau: the subdifferential of f ∈ Γ₀(H) is maximally monotone) — PDF page 361 of `/app/corpus/convex_analysis_and_monotone_operator_theory_in_hilbert_spaces.pdf`.

Put it in `/app/autoformalize/LeanWorkspace/BC_chap_20_25.lean`, the file should have a theorem named `BC_chap_20_25` whose proof is `sorry`. Do not prove it. The project keeps its definitions in `/app/autoformalize/LeanWorkspace/Defs.lean`.

Formalize this at a suitable level of generality. Your statement will become part of a project that formalizes results from every source in the corpus.

The project already contains formalizations of other results in the corpus. You may edit them, but the package must still build.

**Time.** 30 minutes. Whatever is on disk at the end is your submission.

## Environment

- `/app/corpus/` holds the books and papers as PDFs (titles in `/app/corpus/INDEX.md`).
- The Lake package is `/app/autoformalize/` (Lean v4.28.0, Mathlib prebuilt). Check your file with `lake env lean LeanWorkspace/BC_chap_20_25.lean` or `lake build LeanWorkspace` from there.
- Web access is permitted.
- `/app/scratch/` is for notes and extracted text; it is not assessed.

## Format (checked by `submit` and the grader)

We will check that `lake build LeanWorkspace` succeeds and the file has a single theorem `BC_chap_20_25` whose proof is `sorry`.
