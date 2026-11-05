# Prove `FCA_chap_E_1_3_1_viii`

You are given a Lean theorem with `sorry` in place of its proof. Produce a Lean proof of that theorem.

## Problem statement

`LeanWorkspace/FCA_chap_E_1_3_1_viii.lean` contains the definitions the statement depends on, followed by the theorem `FCA_chap_E_1_3_1_viii`.

## Success criteria

1. `lake build LeanWorkspace`, run from the project root, exits successfully.
2. `LeanWorkspace.lean`, `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` are unchanged, and so are the theorem statement and the given definitions.
3. `#print axioms` on the theorem you prove -- `FCA_chap_E_1_3_1_viii` -- reports no `sorryAx` and no axiom beyond Lean's own `propext`, `Classical.choice`, and `Quot.sound`.
4. No `native_decide`.
5. Lean comparator accepts the proof.
