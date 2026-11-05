# Formalize Proposition B.1.2.1 (Hiriart-Urruty & Lemaréchal, Fundamentals of Convex Analysis)

Write a Lean 4 statement of **Proposition B.1.2.1** from Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Chapter B, Section 1.2, Proposition 1.2.1 (every f ∈ Conv ℝⁿ has an affine minorant; subgradient at relative interior points) — PDF page 87 of `/app/corpus/fundamentals_of_convex_analysis.pdf`.

Put it in `/app/autoformalize/LeanWorkspace/FCA_chap_B_1_2_1.lean`, the file should have a theorem named `FCA_chap_B_1_2_1` whose proof is `sorry`. Do not prove it. The project keeps its definitions in `/app/autoformalize/LeanWorkspace/Defs.lean`.

Formalize this at a suitable level of generality. Your statement will become part of a project that formalizes results from every source in the corpus.

**Time.** 30 minutes. Whatever is on disk at the end is your submission.

## Environment

- `/app/corpus/` holds the books and papers as PDFs (titles in `/app/corpus/INDEX.md`).
- The Lake package is `/app/autoformalize/` (Lean v4.28.0, Mathlib prebuilt). Check your file with `lake env lean LeanWorkspace/FCA_chap_B_1_2_1.lean` or `lake build LeanWorkspace` from there.
- Web access is permitted.
- `/app/scratch/` is for notes and extracted text; it is not assessed.

## Format (checked by `submit` and the grader)

We will check that `lake build LeanWorkspace` succeeds and the file has a single theorem `FCA_chap_B_1_2_1` whose proof is `sorry`.
