/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.Parse
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Gcd
import Azurite.AzNat.Compare
import Azurite.AzZMod.Basic
import Azurite.AzZMod.Pow
import Azurite.AzZMod.Quad
import Azurite.AzZMod.ToString
import Azurite.AzZMod.Sqrt
import Azurite.AzNat.IsPrime

/-!
# Checks for Malachite's `mod_*` operations against `AzZMod`

The general-modulus companion of `Azurite.Oracle.AzZModPow2`: Malachite's `mod_add`, `mod_mul`,
and the rest are `Natural` operations taking the modulus as an argument and requiring reduced
inputs, and each check wraps the printed inputs as `AzZMod m` values (a disagreement if one is
unreduced or the modulus is zero, neither of which the demos' generators produce) and compares the
type's operation with the printed result. The correspondence is documented on Malachite's
"Malachite for Azurite Users: Integers Modulo a Natural" page.
-/

namespace Azurite.Oracle

open Azurite

/-- The `NeZero` instance the residue operations need, for a printed modulus (lifted out of
`Prop` so that it can be the value of an `Except`). -/
def modulus (m : AzNat) : Except Failure (PLift (NeZero m.toNat)) :=
  if h : m.toNat = 0 then disagree "the modulus is zero" else pure ⟨⟨h⟩⟩

/-- `x` as a residue modulo `m`, which Malachite's modular operations require to be reduced. -/
def residueMod (m : AzNat) [NeZero m.toNat] (what : String) (x : AzNat) :
    Except Failure (AzZMod m) :=
  let a := AzZMod.ofAzNat m x
  if a.val == x then pure a else disagree s!"{what} = {x} is not reduced mod {m}"

/-- Takes apart `lhs ≡ z mod m`, returning the left-hand side as a string; the modulus may be
printed as `&m`. -/
def congruenceModLine (line : String) : Except Failure (String × AzNat × AzNat) := do
  let (lhs, rest) ← match line.splitOn " ≡ " with
    | [lhs, rest] => pure (lhs, rest)
    | _ => fail "not an `lhs ≡ z mod m` line"
  let (z, m) ← match rest.splitOn " mod " with
    | [z, m] => pure (z, m)
    | _ => fail "not an `lhs ≡ z mod m` line"
  let z ← expect "z" (parseAzNat z)
  let m ← expect "m" (parseAzNat (stripRef m))
  pure (lhs, z, m)

/-! ### Ring operations -/

/-- `x op y ≡ z mod m` for a ring operation of `AzZMod m`. -/
def checkModOp (op : String)
    (f : {m : AzNat} → [NeZero m.toNat] → AzZMod m → AzZMod m → AzZMod m) (line : String) :
    Verdict := do
  let (lhs, z, m) ← congruenceModLine line
  let (x, y) ← match lhs.splitOn s!" {op} " with
    | [x, y] => pure (stripRef x, stripRef y)
    | _ => fail s!"not an `x {op} y` left-hand side"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let a ← residueMod m "x" x
  let b ← residueMod m "y" y
  expectEq s!"x {op} y mod m" (f a b).val z

def checkModAdd : String → Verdict := checkModOp "+" AzZMod.add

def checkModSub : String → Verdict := checkModOp "-" AzZMod.sub

def checkModMul : String → Verdict := checkModOp "*" AzZMod.mul

/-- `x.square() ≡ z mod m`, the receiver possibly printed as `(&x)`. -/
def checkModSquare (line : String) : Verdict := do
  let (lhs, z, m) ← congruenceModLine line
  if !lhs.endsWith ".square()" then fail "not an `x.square()` left-hand side"
  let x ← expect "x" (parseAzNat (stripRef (dropRightChars lhs 9)))
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let a ← residueMod m "x" x
  expectEq "square mod m" (Square.square a).val z

/-- `-x ≡ z mod m`, the left-hand side possibly printed as `&(-x)`. -/
def checkModNeg (line : String) : Verdict := do
  let (lhs, z, m) ← congruenceModLine line
  let lhs := stripRef lhs
  if !lhs.startsWith "-" then fail "not a `-x` left-hand side"
  let x ← expect "x" (parseAzNat (stripRef (dropChars lhs 1)))
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let a ← residueMod m "x" x
  expectEq "neg mod m" (AzZMod.neg a).val z

/-- `x.pow(e) ≡ z mod m`, with a natural exponent: `powAzNat`. -/
def checkModPow (line : String) : Verdict := do
  let (lhs, z, m) ← congruenceModLine line
  let (x, e) ← match lhs.splitOn ".pow(" with
    | [x, rest] =>
      if rest.endsWith ")" then pure (stripRef x, dropRightChars rest 1)
      else fail "not an `x.pow(e)` left-hand side"
    | _ => fail "not an `x.pow(e)` left-hand side"
  let x ← expect "x" (parseAzNat x)
  let e ← expect "exponent" (parseAzNat e)
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let a ← residueMod m "x" x
  expectEq "pow mod m" (AzZMod.powAzNat a e).val z

/-- `x⁻¹ ≡ i mod m`, or `x is not invertible mod m`: `tryInv`, which is `none` exactly when `x`
and `m` are not coprime. -/
def checkModInv (line : String) : Verdict :=
  match line.splitOn " is not invertible mod " with
  | [x, m] => do
    let x ← expect "x" (parseAzNat (stripRef x))
    let m ← expect "m" (parseAzNat (stripRef m))
    let hm ← modulus m
    have : NeZero m.toNat := hm.down
    let a ← residueMod m "x" x
    expectEq "is invertible" (AzZMod.tryInv a).isSome false
  | _ => do
    let (lhs, inverse, m) ← congruenceModLine line
    if !lhs.endsWith "⁻¹" then fail "not an `x⁻¹` left-hand side"
    let x ← expect "x" (parseAzNat (stripRef (dropRightChars lhs 2)))
    let hm ← modulus m
    have : NeZero m.toNat := hm.down
    let a ← residueMod m "x" x
    match AzZMod.tryInv a with
    | some i => expectEq "inverse mod m" i.val inverse
    | none => disagree s!"{x} and {m} are not coprime, so there is no inverse"

/-! ### The precomputed variants -/

/-- The receiver, the first two arguments, and the result of a `_precomputed` call, whose last
argument is the precomputed data, printed as `&data`. -/
def precomputedCall (line method : String) (arity : Nat) :
    Except Failure (AzNat × List AzNat × AzNat) := do
  let (x, args, res) ← expect s!"an `x.{method}(…, &data) = z` line" (methodCall line method)
  if args.length != arity + 1 then fail s!"{method} takes {arity + 1} arguments"
  let x ← expect "x" (parseAzNat x)
  let args ← expect "arguments" (parseAzNats (args.take arity))
  let z ← expect "z" (parseAzNat res)
  pure (x, args, z)

/-- `x.mod_mul_precomputed(y, m, &data) = z`: the same product as `mod_mul`. -/
def checkModMulPrecomputed (line : String) : Verdict := do
  let (x, args, z) ← precomputedCall line "mod_mul_precomputed" 2
  let (y, m) ← match args with
    | [y, m] => pure (y, m)
    | _ => fail "mod_mul_precomputed takes two operands"
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let a ← residueMod m "x" x
  let b ← residueMod m "y" y
  expectEq "mod_mul_precomputed" (AzZMod.mul a b).val z

/-- `x.mod_square_precomputed(m, &data) = z`: the same square as `mod_square`. -/
def checkModSquarePrecomputed (line : String) : Verdict := do
  let (x, args, z) ← precomputedCall line "mod_square_precomputed" 1
  let m ← match args with
    | [m] => pure m
    | _ => fail "mod_square_precomputed takes one operand"
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let a ← residueMod m "x" x
  expectEq "mod_square_precomputed" (Square.square a).val z

/-- `x.mod_pow_precomputed(e, m, &data) = z`: the same power as `mod_pow`. -/
def checkModPowPrecomputed (line : String) : Verdict := do
  let (x, args, z) ← precomputedCall line "mod_pow_precomputed" 2
  let (e, m) ← match args with
    | [e, m] => pure (e, m)
    | _ => fail "mod_pow_precomputed takes two operands"
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let a ← residueMod m "x" x
  expectEq "mod_pow_precomputed" (AzZMod.powAzNat a e).val z

/-! ### Shifts, division, reducedness, and equality -/

/-- `x.mod_shl(s, m) = z` or `x.mod_shr(s, m) = z`: a shift of the representative, reduced, with a
negative count reversing the direction; `AzZMod` has no shift operation, so this is the spelling
the mapping page gives. -/
def checkModShift (method : String) (left : Bool) (line : String) : Verdict := do
  let (x, args, res) ← expect s!"an `x.{method}(s, m) = z` line" (methodCall line method)
  let (s, m) ← match args with
    | [s, m] => pure (s, m)
    | _ => fail s!"{method} takes two arguments"
  let x ← expect "x" (parseAzNat x)
  let s ← expect "shift" (parseInt s)
  let m ← expect "m" (parseAzNat m)
  let z ← expect "z" (parseAzNat res)
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let _ ← residueMod m "x" x
  let shifted :=
    if (s < 0) != left then AzNat.shiftLeft x s.natAbs else AzNat.shiftRight x s.natAbs
  expectEq method (AzZMod.ofAzNat m shifted).val z

def checkModShl : String → Verdict := checkModShift "mod_shl" true

def checkModShr : String → Verdict := checkModShift "mod_shr" false

/-- `x.mod_div(y, m) = Some(q)` or `None`. Malachite documents that a quotient exists exactly when
`gcd(y, m)` divides `x`, and that when `y` is not a unit any of the quotients may be returned, so
the check is of that existence condition and of `q·y ≡ x` for the printed `q`. -/
def checkModDiv (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.mod_div(y, m) = r` line" (methodCall line "mod_div")
  let (y, m) ← match args with
    | [y, m] => pure (y, m)
    | _ => fail "mod_div takes two arguments"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let m ← expect "m" (parseAzNat m)
  let res ← expect "result" (parseOption res)
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let a ← residueMod m "x" x
  let b ← residueMod m "y" y
  let solvable := AzNat.mod x (AzNat.gcd y m) == (0 : AzNat)
  match res with
  | none => expectEq "a quotient exists" solvable false
  | some q =>
    if !solvable then disagree s!"Malachite printed a quotient, but gcd({y}, {m}) ∤ {x}"
    let q ← expect "quotient" (parseAzNat q)
    let qr ← residueMod m "quotient" q
    expectEq "q·y mod m" (AzZMod.mul qr b).val a.val

/-- `x.mod_sqrt(m) = Some(y)` or `None`. Malachite documents that for a prime modulus a root is
returned exactly when one exists, either of the two; for other moduli it may return `None` though a
root exists, or a value that is not a root, so there only the documented range `y < m` is checked.
For a prime modulus (decided by the proven `AzNat.isPrime`), `AzZMod.sqrt?`, complete for primes
and returning the smaller root, decides existence, and the printed root must be it or its
negation. -/
def checkModSqrt (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.mod_sqrt(m) = r` line" (methodCall line "mod_sqrt")
  let m ← match args with
    | [m] => pure (stripRef m)
    | _ => fail "mod_sqrt takes one argument"
  let x ← expect "x" (parseAzNat x)
  let m ← expect "m" (parseAzNat m)
  let res ← expect "result" (parseOption res)
  let hm ← modulus m
  have : NeZero m.toNat := hm.down
  let a ← residueMod m "x" x
  let root ← match res with
    | none => pure none
    | some y => do
      let y ← expect "root" (parseAzNat y)
      let r ← residueMod m "root" y
      pure (some r)
  if AzNat.isPrime m then
    match AzZMod.sqrt? a, root with
    | none, none => pure ()
    | some _, none => disagree s!"{x} is a square mod the prime {m}, but Malachite found no root"
    | none, some y =>
      disagree s!"{x} is not a square mod the prime {m}, but Malachite printed {y.val}"
    | some r, some y =>
      if y.val == r.val || y.val == (-r).val then pure ()
      else disagree s!"the roots of {x} mod {m} are {r.val} and {(-r).val}, not {y.val}"
  else pure ()

/-- `x is reduced mod m` or `x is not reduced mod m`: whether `x < m`. -/
def checkModIsReduced (line : String) : Verdict := do
  let (x, m, expected) ←
    match line.splitOn " is not reduced mod ", line.splitOn " is reduced mod " with
    | [x, m], _ => pure (x, m, false)
    | _, [x, m] => pure (x, m, true)
    | _, _ => fail "not a reducedness line"
  let x ← expect "x" (parseAzNat x)
  let m ← expect "m" (parseAzNat m)
  expectEq "mod_is_reduced" (AzNat.compare x m == .lt) expected

/-- `x is equal to y mod m` or `x is not equal to y mod m`, for unreduced `x` and `y` and any
`&` markers: equality of the residues, or of the values themselves when `m` is zero. -/
def checkModEq (line : String) : Verdict := do
  let (x, rest, expected) ←
    match line.splitOn " is not equal to ", line.splitOn " is equal to " with
    | [x, rest], _ => pure (x, rest, false)
    | _, [x, rest] => pure (x, rest, true)
    | _, _ => fail "not an equality line"
  let (y, m) ← match rest.splitOn " mod " with
    | [y, m] => pure (y, m)
    | _ => fail "not an `… mod m` line"
  let x ← expect "x" (parseAzNat (stripRef x))
  let y ← expect "y" (parseAzNat (stripRef y))
  let m ← expect "m" (parseAzNat (stripRef m))
  if h : m.toNat = 0 then expectEq "eq_mod" (x == y) expected
  else
    have : NeZero m.toNat := ⟨h⟩
    expectEq "eq_mod" (AzZMod.ofAzNat m x == AzZMod.ofAzNat m y) expected

end Azurite.Oracle
