/-
  print_axioms.lean — Collect and print all axioms used by declarations
  in the Azurite namespace.

  Usage: lake env lean scripts/print_axioms.lean
-/
import Azurite

open Lean in
unsafe def collectAllAxioms : IO Unit := do
  let env ← importModules #[{ module := `Azurite }] {}
  -- Collect axioms transitively for every Azurite.* declaration
  let mut allAxioms : Std.HashSet Name := {}
  let mut count := 0
  let mut sorry_decls : Array Name := #[]
  for (name, _) in env.constants.map₁.toList do
    if name.getRoot == `Azurite && !name.isInternal then
      count := count + 1
      let axioms := collectAxioms env name
      for ax in axioms do
        allAxioms := allAxioms.insert ax
        if ax == `sorryAx then
          sorry_decls := sorry_decls.push name
  IO.println s!"Checked {count} declarations in Azurite.*"
  IO.println ""
  IO.println "Axioms used:"
  for ax in allAxioms.toList.mergeSort (·.toString < ·.toString) do
    IO.println s!"  {ax}"
  if sorry_decls.size > 0 then
    IO.println ""
    IO.println s!"⚠ WARNING: {sorry_decls.size} declaration(s) use sorry:"
    for d in sorry_decls do
      IO.println s!"  {d}"
  else
    IO.println ""
    IO.println "✓ No declarations use sorry."
where
  collectAxioms (env : Environment) (root : Name) : List Name :=
    let (_, axs) := go env root ({}, [])
    axs
  go (env : Environment) (name : Name) : (Std.HashSet Name × List Name) →
      (Std.HashSet Name × List Name)
    | (visited, acc) =>
      if visited.contains name then (visited, acc)
      else
        let visited := visited.insert name
        match env.constants.find? name with
        | some (.axiomInfo _) => (visited, name :: acc)
        | some ci =>
          let used := ci.getUsedConstantsAsSet.toArray
          used.foldl (init := (visited, acc))
            fun state u => go env u state
        | none => (visited, acc)

#eval collectAllAxioms
