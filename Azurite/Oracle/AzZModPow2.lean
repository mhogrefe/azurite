/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.Parse
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzZModPow2.Basic
import Azurite.AzZModPow2.Conversion
import Azurite.AzZModPow2.Inv
import Azurite.AzZModPow2.Pow
import Azurite.AzZModPow2.ToString
import Azurite.AzZModPow2.Sqrt

/-!
# Checks for Malachite's `mod_power_of_2_*` operations against `AzZModPow2`

Malachite has no residue type: its arithmetic modulo `2^k` is a family of `Natural` operations
that take `k` as an argument and require their inputs to be reduced. Each check here reads such a
line, requires the printed inputs to be reduced (a disagreement otherwise, since the demo's
generator promises reduced inputs), wraps them as `AzZModPow2 k` values, and compares the type's
operation with the printed result. The correspondence is documented on Malachite's "Malachite for
Azurite Users: Integers Modulo a Power of 2" page.
-/

namespace Azurite.Oracle

open Azurite

/-- `x` as a residue modulo `2^k`, which Malachite's modular operations require to be reduced. -/
def residue (k : Nat) (what : String) (x : AzNat) : Except Failure (AzZModPow2 k) :=
  let a := AzZModPow2.ofAzNat k x
  if a.val == x then pure a else disagree s!"{what} = {x} is not reduced mod 2^{k}"

/-- Takes apart `lhs ≡ z mod 2^k`, returning the left-hand side as a string. -/
def congruenceLine (line : String) : Except Failure (String × AzNat × Nat) := do
  let (lhs, rest) ← match line.splitOn " ≡ " with
    | [lhs, rest] => pure (lhs, rest)
    | _ => fail "not an `lhs ≡ z mod 2^k` line"
  let (z, k) ← match rest.splitOn " mod 2^" with
    | [z, k] => pure (z, k)
    | _ => fail "not an `lhs ≡ z mod 2^k` line"
  let z ← expect "z" (parseAzNat z)
  let k ← expect "k" (parseNat k)
  pure (lhs, z, k)

/-! ### Ring operations -/

/-- `x op y ≡ z mod 2^k` for a ring operation of `AzZModPow2 k`. -/
def checkZModOp (op : String) (f : {k : Nat} → AzZModPow2 k → AzZModPow2 k → AzZModPow2 k)
    (line : String) : Verdict := do
  let (lhs, z, k) ← congruenceLine line
  let (x, y) ← match lhs.splitOn s!" {op} " with
    | [x, y] => pure (stripRef x, stripRef y)
    | _ => fail s!"not an `x {op} y` left-hand side"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let a ← residue k "x" x
  let b ← residue k "y" y
  expectEq s!"x {op} y mod 2^k" (f a b).val z

def checkZModAdd : String → Verdict := checkZModOp "+" AzZModPow2.add

def checkZModSub : String → Verdict := checkZModOp "-" AzZModPow2.sub

def checkZModMul : String → Verdict := checkZModOp "*" AzZModPow2.mul

/-- `x.square() ≡ z mod 2^k`, the receiver possibly printed as `(&x)`. -/
def checkZModSquare (line : String) : Verdict := do
  let (lhs, z, k) ← congruenceLine line
  if !lhs.endsWith ".square()" then fail "not an `x.square()` left-hand side"
  let x ← expect "x" (parseAzNat (stripRef (dropRightChars lhs 9)))
  let a ← residue k "x" x
  expectEq "square mod 2^k" (Square.square a).val z

/-- `-x ≡ z mod 2^k`, the operand possibly printed as `(&x)`. -/
def checkZModNeg (line : String) : Verdict := do
  let (lhs, z, k) ← congruenceLine line
  if !lhs.startsWith "-" then fail "not a `-x` left-hand side"
  let x ← expect "x" (parseAzNat (stripRef (dropChars lhs 1)))
  let a ← residue k "x" x
  expectEq "neg mod 2^k" (AzZModPow2.neg a).val z

/-- `x.pow(e) ≡ z mod 2^k`; Malachite's exponent is a `Natural`, read here as a `Nat`. -/
def checkZModPow (line : String) : Verdict := do
  let (lhs, z, k) ← congruenceLine line
  let (x, e) ← match lhs.splitOn ".pow(" with
    | [x, rest] =>
      if rest.endsWith ")" then pure (stripRef x, dropRightChars rest 1)
      else fail "not an `x.pow(e)` left-hand side"
    | _ => fail "not an `x.pow(e)` left-hand side"
  let x ← expect "x" (parseAzNat x)
  let e ← expect "exponent" (parseNat e)
  let a ← residue k "x" x
  expectEq "pow mod 2^k" (AzZModPow2.pow a e).val z

/-- `x⁻¹ ≡ i mod 2^k`, or `x is not invertible mod 2^k`: a residue is a unit exactly when it is
odd, and `invOdd` inverts the odd ones. -/
def checkZModInverse (line : String) : Verdict :=
  match line.splitOn " is not invertible mod 2^" with
  | [x, k] => do
    let x ← expect "x" (parseAzNat (stripRef x))
    let k ← expect "k" (parseNat k)
    let a ← residue k "x" x
    expectEq "is invertible" a.isOdd false
  | _ => do
    let (lhs, inverse, k) ← congruenceLine line
    if !lhs.endsWith "⁻¹" then fail "not an `x⁻¹` left-hand side"
    let x ← expect "x" (parseAzNat (stripRef (dropRightChars lhs 2)))
    let a ← residue k "x" x
    if h : a.isOdd = true then expectEq "inverse mod 2^k" (AzZModPow2.invOdd a h).val inverse
    else disagree s!"{x} is even, so it has no inverse mod 2^{k}"

/-- `x.mod_power_of_2_sqrt(k) = Some(r)` or `None`. Both libraries return the least root, so the
printed result is compared with `AzZModPow2.sqrt?` exactly. -/
def checkZModSqrt (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.mod_power_of_2_sqrt(k) = r` line"
    (methodCall line "mod_power_of_2_sqrt")
  let k ← match args with
    | [k] => expect "k" (parseNat k)
    | _ => fail "mod_power_of_2_sqrt takes one argument"
  let x ← expect "x" (parseAzNat x)
  let res ← expect "result" (parseOption res)
  let a ← residue k "x" x
  let printed ← match res with
    | none => pure none
    | some r => do
      let r ← expect "root" (parseAzNat r)
      pure (some r)
  match AzZModPow2.sqrt? a, printed with
  | none, none => pure ()
  | some r, none => disagree s!"{x} has the root {r.val} mod 2^{k}, but Malachite printed None"
  | none, some r => disagree s!"{x} is not a square mod 2^{k}, but Malachite printed {r}"
  | some r, some p => expectEq "least root mod 2^k" r.val p

/-! ### Shifts, reducedness, and equality -/

/-- `x.mod_power_of_2_shl(s, k) = z`: `x · 2^s` reduced, or a right shift for negative `s`.
`AzZModPow2` has no shift operation, so this is the spelling the mapping page gives. -/
def checkZModShl (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.mod_power_of_2_shl(s, k) = z` line"
    (methodCall line "mod_power_of_2_shl")
  let (s, k) ← match args with
    | [s, k] => pure (s, k)
    | _ => fail "mod_power_of_2_shl takes two arguments"
  let x ← expect "x" (parseAzNat x)
  let s ← expect "shift" (parseInt s)
  let k ← expect "k" (parseNat k)
  let z ← expect "z" (parseAzNat res)
  let _ ← residue k "x" x
  let shifted := if s < 0 then AzNat.shiftRight x (-s).toNat else AzNat.shiftLeft x s.toNat
  expectEq "mod_power_of_2_shl" (AzZModPow2.ofAzNat k shifted).val z

/-- `x.mod_power_of_2_shr(s, k) = z`: the floor of `x / 2^s`, or a left shift for negative `s`. -/
def checkZModShr (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.mod_power_of_2_shr(s, k) = z` line"
    (methodCall line "mod_power_of_2_shr")
  let (s, k) ← match args with
    | [s, k] => pure (s, k)
    | _ => fail "mod_power_of_2_shr takes two arguments"
  let x ← expect "x" (parseAzNat x)
  let s ← expect "shift" (parseInt s)
  let k ← expect "k" (parseNat k)
  let z ← expect "z" (parseAzNat res)
  let _ ← residue k "x" x
  let shifted := if s < 0 then AzNat.shiftLeft x (-s).toNat else AzNat.shiftRight x s.toNat
  expectEq "mod_power_of_2_shr" (AzZModPow2.ofAzNat k shifted).val z

/-- `x is reduced mod 2^k` or `x is not reduced mod 2^k`: whether `ofAzNat` leaves `x` alone. -/
def checkZModIsReduced (line : String) : Verdict := do
  let (x, k, expected) ←
    match line.splitOn " is not reduced mod 2^", line.splitOn " is reduced mod 2^" with
    | [x, k], _ => pure (x, k, false)
    | _, [x, k] => pure (x, k, true)
    | _, _ => fail "not a reducedness line"
  let x ← expect "x" (parseAzNat x)
  let k ← expect "k" (parseNat k)
  expectEq "mod_power_of_2_is_reduced" ((AzZModPow2.ofAzNat k x).val == x) expected

/-- `x is equal to y mod 2^k` or `x is not equal to y mod 2^k`, for unreduced `x` and `y`:
equality of the residues. -/
def checkZModEq (line : String) : Verdict := do
  let (rest, expected) ←
    match line.splitOn " is not equal to ", line.splitOn " is equal to " with
    | [x, rest], _ => pure ((x, rest), false)
    | _, [x, rest] => pure ((x, rest), true)
    | _, _ => fail "not an equality line"
  let (x, rest) := rest
  let (y, k) ← match rest.splitOn " mod 2^" with
    | [y, k] => pure (y, k)
    | _ => fail "not an `… mod 2^k` line"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let k ← expect "k" (parseNat k)
  expectEq "eq_mod_power_of_2" (AzZModPow2.ofAzNat k x == AzZModPow2.ofAzNat k y) expected

/-! ### Conversion -/

/-- `z.mod_power_of_2(k) = n` for an integer `z`: `ofAzInt`, whose residue is the `Natural`
Malachite returns. -/
def checkZModOfInt (line : String) : Verdict := do
  let (z, args, res) ← expect "a `z.mod_power_of_2(k) = n` line"
    (methodCall line "mod_power_of_2")
  let k ← match args with
    | [k] => pure k
    | _ => fail "mod_power_of_2 takes one argument"
  let z ← expect "z" (parseAzInt z)
  let k ← expect "k" (parseNat k)
  let n ← expect "n" (parseAzNat res)
  expectEq "mod_power_of_2" (AzZModPow2.ofAzInt k z).val n

end Azurite.Oracle
