/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  check_axioms.lean — Verify that every declaration in the Azurite
  namespace depends only on allowed axioms.

  Allowed axioms: the standard three — `propext`, `Classical.choice`,
  `Quot.sound` — and nothing else.  In particular `native_decide`
  (which mints `Lean.ofReduceBool`-based auxiliary axioms) is NOT
  permitted: Azurite eliminated its last use in July 2026 (the
  Möller–Granlund reciprocal table is now kernel-checked pointwise),
  and this script keeps it out.

  Anything else — `sorryAx`, a `native_decide` auxiliary, or a newly
  introduced user axiom — is an error: the offending declarations are
  listed and the script exits with a non-zero code, failing CI.

  Implementation notes: the dependency cone is walked with an explicit
  work list (no recursion, so no stack-depth limit, and immune to the
  reference cycles that mutually-recursive definitions produce in
  `getUsedConstantsAsSet`). Constants whose cone has been verified clean
  are recorded in a shared set, so later declarations skip already
  verified regions and the whole check is a single pass over the
  environment in the common (all-clean) case.

  Usage: lake env lean scripts/check_axioms.lean
-/
import Azurite

open Lean

/-- Axioms that Azurite declarations are allowed to depend on: the
    standard three, nothing more. -/
def allowedAxioms : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

/-- An axiom is allowed only if it is in the fixed list (no
    `native_decide` auxiliaries). -/
def isAllowedAxiom (n : Name) : Bool :=
  allowedAxioms.contains n

unsafe def checkAllAxioms : IO Unit := do
  let env ← importModules #[{ module := `Azurite }] {}
  -- Constants whose entire dependency cone is known to use only allowed
  -- axioms. Grows monotonically across the outer loop.
  let mut clean : Std.HashSet Name := {}
  let mut allAxioms : Std.HashSet Name := {}
  let mut violations : Array (Name × List Name) := #[]
  let mut count := 0
  for (root, _) in env.constants.map₁.toList do
    if root.getRoot == `Azurite && !root.isInternal then
      count := count + 1
      if clean.contains root then
        continue
      -- Iterative DFS over the dependency cone of `root`.
      let mut visited : Std.HashSet Name := {}
      let mut bad : Std.HashSet Name := {}
      let mut stack : Array Name := #[root]
      while true do
        let some n := stack.back? | break
        stack := stack.pop
        if visited.contains n || clean.contains n then
          continue
        visited := visited.insert n
        match env.constants.find? n with
        | some (.axiomInfo _) =>
            allAxioms := allAxioms.insert n
            if !isAllowedAxiom n then
              bad := bad.insert n
        | some ci =>
            for u in ci.getUsedConstantsAsSet do
              if !visited.contains u && !clean.contains u then
                stack := stack.push u
        | none => pure ()
      if bad.isEmpty then
        -- Everything reachable from `root` is verified clean; never
        -- traverse any of it again.
        for n in visited do
          clean := clean.insert n
      else
        violations := violations.push (root, bad.toList.mergeSort (·.toString < ·.toString))
  IO.println s!"Checked {count} declarations in Azurite.*"
  IO.println ""
  IO.println "Axioms used:"
  for ax in allAxioms.toList.mergeSort (·.toString < ·.toString) do
    let tag := if isAllowedAxiom ax then "" else "   ← NOT ALLOWED"
    IO.println s!"  {ax}{tag}"
  if violations.size > 0 then
    IO.println ""
    IO.println s!"✗ {violations.size} declaration(s) depend on disallowed axioms:"
    for (d, axs) in (violations.qsort (·.1.toString < ·.1.toString)) do
      IO.println s!"  {d}: {axs}"
    throw <| IO.userError "Axiom check failed."
  IO.println ""
  IO.println "✓ All declarations use only allowed axioms."

#eval checkAllAxioms
