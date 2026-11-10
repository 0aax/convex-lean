# ConvexStarLib

A Lean 4 library (Lean `v4.28.0`, Mathlib `v4.28.0`) of 315 textbook results in convex
analysis, optimization, and geometry, each with a complete proof. The statements are the
`convex-eval-v28-2h` tasks of this repository and the proofs are the ones the grader accepted
from the 2-hour Claude Code runs.

## Build

From this directory:

```
lake exe cache get   # Mathlib oleans
lake build
lake env lean scripts/AxiomCheck.lean
```

## Layout

```
ConvexStarLib.lean                root: imports Defs and every book
ConvexStarLib/Defs.lean           shared definitions used by every statement
ConvexStarLib/<Book>.lean         imports the theorems of one source
ConvexStarLib/<Book>/<name>.lean  one theorem per textbook result
scripts/AxiomCheck.lean           checks that every main theorem uses only the standard axioms
docbuild/                         doc-gen4 project that renders the documentation site
../.github/workflows/docs.yml     builds the documentation and deploys it to GitHub Pages
```

| folder | source | theorems |
| --- | --- | --- |
| `FCA` | Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis* | 173 |
| `CAMA` | Hiriart-Urruty & Lemaréchal, *Convex Analysis and Minimization Algorithms I* | 38 |
| `RW` | Rockafellar & Wets, *Variational Analysis* | 33 |
| `Bubeck` | Bubeck, *Convex Optimization: Algorithms and Complexity* | 32 |
| `Duchi` | Duchi, EE364m Mathematics of Convexity (exercise sets) | 13 |
| `Renegar` | Renegar, *A Mathematical View of Interior-Point Methods* (chap. 2) | 11 |
| `BC` | Bauschke & Combettes, *Convex Analysis and Monotone Operator Theory in Hilbert Spaces* | 7 |
| `BrunnMinkowski` | Brunn–Minkowski, Prékopa–Leindler and Grünbaum inequalities | 4 |
| `Alg` | SAG (Schmidt, Le Roux & Bach) and SAGA (Defazio, Bach & Lacoste-Julien) convergence bounds | 4 |

Each theorem file imports `ConvexStarLib.Defs`, keeps the `open` and `variable` lines of
its statement, and is wrapped in `namespace <name>`, so the main result of
`ConvexStarLib/FCA/FCA_chap_A_ex_13.lean` is `FCA_chap_A_ex_13.FCA_chap_A_ex_13`.
