import ConvexStarLib

/-! Run from the project root: `lake env lean scripts/AxiomCheck.lean`.

Every file `ConvexStarLib/<Book>/<T>.lean` proves a main theorem `T.T`. This script
finds those theorems in the environment, reports the axioms they depend on, and fails
if any of them uses an axiom outside `propext`, `Classical.choice` and `Quot.sound`
(in particular `sorryAx`). -/

open Lean Elab Command

/-- The axioms a complete classical proof may use. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The main theorem of each `ConvexStarLib.<Book>.<T>` module, namely `T.T`. -/
def mainTheorems (env : Environment) : Except String (Array Name) := do
  let mut thms := #[]
  for mod in env.allImportedModuleNames do
    if let .str (.str (.str .anonymous "ConvexStarLib") _book) task := mod then
      let thm := Name.mkStr (Name.mkStr .anonymous task) task
      unless env.contains thm do
        throw s!"{mod}: main theorem {thm} not found"
      thms := thms.push thm
  return thms

elab "#check_main_theorem_axioms" : command => do
  let env ← getEnv
  let thms ← match mainTheorems env with
    | .ok thms => pure thms
    | .error e => throwError e
  -- Group the theorems by the exact set of axioms they use.
  let mut groups : Array (Array Name × Array Name) := #[]
  let mut bad : Array (Name × Array Name) := #[]
  for thm in thms do
    let axioms := (← collectAxioms thm).qsort (toString · < toString ·)
    match groups.findIdx? (·.1 == axioms) with
    | some i => groups := groups.modify i fun (a, ts) => (a, ts.push thm)
    | none => groups := groups.push (axioms, #[thm])
    let extra := axioms.filter (!allowedAxioms.contains ·)
    unless extra.isEmpty do
      bad := bad.push (thm, extra)
  for (axioms, ts) in groups do
    logInfo m!"{ts.size} theorem(s) use {axioms}"
  unless bad.isEmpty do
    throwError "main theorems using axioms outside {allowedAxioms}:\n{bad}"
  logInfo m!"checked {thms.size} main theorems"

#check_main_theorem_axioms
