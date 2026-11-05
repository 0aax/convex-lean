# Prove `sag_strongly_convex_linear_bound`

You are given a Lean theorem with `sorry` in place of its proof. Produce a Lean proof of that theorem.

## Problem statement

`LeanWorkspace/sag_strongly_convex_linear_bound.lean` contains the definitions the statement depends on, followed by the theorem `sag_strongly_convex_linear_bound`.

## Success criteria

1. `lake build LeanWorkspace`, run from the project root, exits successfully.
2. `LeanWorkspace.lean`, `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` are unchanged, and so are the theorem statement and the given definitions.
3. `#print axioms` on the theorem you prove -- `sag_strongly_convex_linear_bound` -- reports no `sorryAx` and no axiom beyond Lean's own `propext`, `Classical.choice`, and `Quot.sound`.
4. No `native_decide`.
5. Lean comparator accepts the proof.
