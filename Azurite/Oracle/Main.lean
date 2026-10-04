/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.AzNat

/-!
# The Malachite oracle

`lake exe oracle <mode> <file>` reads the lines a Malachite demo printed to `<file>`, recomputes
each one with Azurite, and exits nonzero on the first disagreement. It is the Azurite backend of
Malachite's differential-testing driver (`oracle-test/` in the Malachite repository), which runs each
demo in its generator modes and hands the output here. Azurite's results are proven correct, so a
disagreement is a bug in Malachite, in the demo's output format, or in this oracle's reading of
Malachite's conventions.

Every mode is strict: a nonempty line it does not recognize is an error, and so is an input in
which no line was checked, so that a change in a demo's format cannot make a run pass without
checking anything.
-/

open Azurite.Oracle

/-- A mode: its check, and whether a record may span several physical lines. The string demos
print their input string bare, and a randomly generated string may contain a newline; such a
record is read by joining lines until the check accepts the text, up to `maxJoinedLines`, which
keeps the mode strict (a malformed line never parses, however many lines follow it). -/
structure Mode where
  check : String → Verdict
  multiline : Bool := false

def mode (check : String → Verdict) : Mode := { check }

def multiline (check : String → Verdict) : Mode := { check, multiline := true }

/-- The most physical lines one multiline record may span. -/
def maxJoinedLines : Nat := 64

/-- The modes, named after the `AzNat` operation each checks. -/
def modes : List (String × Mode) := [
  ("az_nat_add", mode checkAdd),
  ("az_nat_sub", mode checkSub),
  ("az_nat_saturating_sub", mode checkSaturatingSub),
  ("az_nat_mul", mode checkMul),
  ("az_nat_square", mode checkSquare),
  ("az_nat_pow", mode checkPow),
  ("az_nat_div", mode checkDiv),
  ("az_nat_mod", mode checkMod),
  ("az_nat_div_mod", mode checkDivMod),
  ("az_nat_div_round", mode checkDivRound),
  ("az_nat_shr_round", mode checkShrRound),
  ("az_nat_gcd", mode checkGcd),
  ("az_nat_coprime_with", mode checkCoprimeWith),
  ("az_nat_mod_inverse", mode checkModInverse),
  ("az_nat_jacobi_symbol", mode checkJacobiSymbol),
  ("az_nat_multi_crt", mode checkMultiCrt),
  ("az_nat_mod_power_of_2", mode checkModPowerOf2),
  ("az_nat_mod_power_of_2_add", mode checkModPowerOf2Add),
  ("az_nat_mod_power_of_2_sub", mode checkModPowerOf2Sub),
  ("az_nat_mod_power_of_2_mul", mode checkModPowerOf2Mul),
  ("az_nat_mod_power_of_2_square", mode checkModPowerOf2Square),
  ("az_nat_floor_sqrt", mode checkFloorSqrt),
  ("az_nat_sqrt_rem", mode checkSqrtRem),
  ("az_nat_floor_root", mode checkFloorRoot),
  ("az_nat_checked_root", mode checkCheckedRoot),
  ("az_nat_power_of_2", mode checkPowerOf2),
  ("az_nat_is_power_of_2", mode checkIsPowerOf2),
  ("az_nat_parity", mode checkParity),
  ("az_nat_divisible_by_power_of_2", mode checkDivisibleByPowerOf2),
  ("az_nat_significant_bits", mode checkSignificantBits),
  ("az_nat_trailing_zeros", mode checkTrailingZeros),
  ("az_nat_low_mask", mode checkLowMask),
  ("az_nat_limbs", mode checkLimbs),
  ("az_nat_from_limbs_asc", mode checkFromLimbsAsc),
  ("az_nat_to_digits_asc", mode checkToDigitsAsc),
  ("az_nat_from_string_base", multiline checkFromStringBase),
  ("az_nat_from_str", multiline checkFromStr),
  ("az_nat_to_string_base", mode checkToStringBase),
  ("az_nat_cmp", mode checkCmp),
  ("az_nat_cmp_normalized", mode checkCmpNormalized),
  ("az_nat_from_unsigned", mode checkFromUnsigned),
  ("az_nat_saturating_from_signed", mode checkSaturatingFromSigned),
  ("az_nat_wrapping_from", mode checkWrappingFrom)]

/-- Reports a disagreement or an unreadable record and the text it concerns. -/
def report (name : String) (lineNumber : Nat) (msg text : String) : IO UInt32 := do
  IO.eprintln s!"error in {name} test, line {lineNumber}: {msg}"
  IO.eprintln s!"  {text}"
  return 1

/-- Checks every nonempty record of `path` with the mode's check, reporting the first
disagreement. -/
def runMode (name : String) (m : Mode) (path : String) : IO UInt32 := do
  let lines ← IO.FS.lines ⟨path⟩
  let mut checked := 0
  let mut lineNumber := 0
  -- a multiline record in progress: its text so far, its first line's number, and its line count
  let mut pending : Option (String × Nat × Nat) := none
  for line in lines do
    lineNumber := lineNumber + 1
    match pending with
    | some (text, start, count) =>
      let text := text ++ "\n" ++ line
      match m.check text with
      | .ok () =>
        checked := checked + 1
        pending := none
      | .error (.disagreement msg) => return ← report name start msg text
      | .error (.unreadable msg) =>
        if count + 1 ≥ maxJoinedLines then return ← report name start msg text
        pending := some (text, start, count + 1)
    | none =>
      if (trim line).isEmpty then continue
      match m.check line with
      | .ok () => checked := checked + 1
      | .error (.disagreement msg) => return ← report name lineNumber msg line
      | .error (.unreadable msg) =>
        if m.multiline then pending := some (line, lineNumber, 1)
        else return ← report name lineNumber msg line
  if let some (text, start, _) := pending then
    return ← report name start "the record never became readable" text
  if checked == 0 then
    IO.eprintln s!"error in {name} test: no line of the input had the expected shape"
    return 1
  IO.println s!"{name}: {checked} lines agree with Azurite"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [name, path] =>
    match modes.lookup name with
    | some m => runMode name m path
    | none =>
      IO.eprintln s!"Unknown mode: '{name}'"
      IO.eprintln s!"Valid modes: {modes.map (·.1)}"
      return 2
  | _ =>
    IO.eprintln "Usage: oracle <mode> <file>"
    IO.eprintln s!"Valid modes: {modes.map (·.1)}"
    return 2
