# Formalize Proposition B.3.2.4, second part (Hiriart-Urruty & Lemaréchal, Fundamentals of Convex Analysis)

Write a Lean 4 statement of **Proposition B.3.2.4, second part** from Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Chapter B, Section 3.2, Proposition 3.2.4, the equivalence between compact sublevel sets and positivity of the asymptotic function — PDF page 117 of `/app/corpus/fundamentals_of_convex_analysis.pdf`.

Put it in `/app/autoformalize/LeanWorkspace/FCA_chap_B_3_2_4_ii.lean`, the file should have a theorem named `FCA_chap_B_3_2_4_ii` whose proof is `sorry`. Do not prove it. The project keeps its definitions in `/app/autoformalize/LeanWorkspace/Defs.lean`.

Formalize this at a suitable level of generality. Your statement will become part of a project that formalizes results from every source in the corpus.

**Time.** 30 minutes. Whatever is on disk at the end is your submission.

## Environment

- `/app/corpus/` holds the books and papers as PDFs (titles in `/app/corpus/INDEX.md`).
- The Lake package is `/app/autoformalize/` (Lean v4.28.0, Mathlib prebuilt). Check your file with `lake env lean LeanWorkspace/FCA_chap_B_3_2_4_ii.lean` or `lake build LeanWorkspace` from there.
- Web access is permitted.
- `/app/scratch/` is for notes and extracted text; it is not assessed.

## Format (checked by `submit` and the grader)

We will check that `lake build LeanWorkspace` succeeds and the file has a single theorem `FCA_chap_B_3_2_4_ii` whose proof is `sorry`.
