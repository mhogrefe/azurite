/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Conversion
import Azurite.AzNat.Mul
import Azurite.AzNat.ParseBase
import Azurite.AzNat.Pow
import Azurite.AzRat.Construct

/-!
# `fromSci`: parsing scientific notation into an `AzRat`

A port of the author's own Malachite `Rational::from_sci_string` (`docs/bibliography.md`), the
inverse of `toSci`.  The accepted language, for a base `b` in `[2, 36]`:

* an optional exponent suffix.  In bases below `15` it is the last `'e'`/`'E'` of the string and
  everything after it; in bases `15` and up (where `'e'` is a digit) it is the last `'+'`/`'-'`
  that is not the first character, which must be preceded by an `'e'`/`'E'`, and everything
  from the sign on.  The exponent is a decimal integer with an optional sign, and must fit in a
  signed 64-bit integer (as in Malachite);
* then at most one `'.'`, not followed by a sign; each digit after it lowers the exponent by one;
* then an optional single `'+'`/`'-'`, then at least one base-`b` digit (letters in either case).

The value is `± n · b^e`, in lowest terms.  Examples (base 10): `"123.4"` is `617/5`,
`"1.23E+2"` is `123`, `"-.00e-1"` is `0`, `"0.3333333333333333"` is exactly that decimal;
`"10e"`, `"++1"`, `"1.0.0"`, `"1e0.1"`, `".+2"` and `""` are rejected.  The helpers are
exposed so that the round-trip proofs (`Equiv/FromSci.lean`) can reason about them one at a
time.
-/

namespace Azurite.AzRat

/-- Split a list at the **last** character satisfying `p`: `some (before, c, after)` with
`before ++ c :: after` the input, or `none` when no character satisfies `p`. -/
def splitLast (p : Char → Bool) : List Char → Option (List Char × Char × List Char)
  | [] => none
  | c :: rest =>
    match splitLast p rest with
    | some (bef, d, aft) => some (c :: bef, d, aft)
    | none => if p c then some ([], c, rest) else none

/-- Split a list at the **first** character satisfying `p`: `some (before, after)` with
`before ++ c :: after` the input, or `none` when no character satisfies `p`. -/
def splitFirst (p : Char → Bool) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if p c then some ([], rest)
    else (splitFirst p rest).map fun (bef, aft) => (c :: bef, aft)

/-- Does `e` fit in a signed 64-bit integer?  Malachite parses exponents as `i64`. -/
def fitsInt64 (e : Int) : Bool := -2 ^ 63 ≤ e && e < 2 ^ 63

/-- An exponent indicator. -/
def isExpChar (c : Char) : Bool := c == 'e' || c == 'E'

/-- A sign. -/
def isSignChar (c : Char) : Bool := c == '+' || c == '-'

/-- One step of the decimal accumulator: `none` stays `none`, a non-digit poisons it. -/
def decimalStep (acc : Option Nat) (c : Char) : Option Nat :=
  match acc with
  | none => none
  | some n => if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none

/-- At least one decimal digit, most significant first. -/
def parseDecimalDigits (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else cs.foldl decimalStep (some 0)

/-- Rust's `i64::from_str`: an optional sign, decimal digits, within the `i64` range. -/
def parseExponent (cs : List Char) : Option Int :=
  let signed : Option Int :=
    match cs with
    | [] => none
    | c :: rest =>
      if c == '+' then (parseDecimalDigits rest).map Int.ofNat
      else if c == '-' then (parseDecimalDigits rest).map fun (n : Nat) => -(n : Int)
      else (parseDecimalDigits cs).map Int.ofNat
  signed.filter fitsInt64

/-- Split off the exponent suffix (Malachite's `preprocess_sci_string`, first half): the
mantissa characters and the exponent (`0` when there is no suffix). -/
def splitExponent (b : UInt64) (cs : List Char) : Option (List Char × Int) :=
  if b < 15 then
    match splitLast isExpChar cs with
    | none => some (cs, 0)
    | some ([], _, _) => none
    | some (mant, _, expChars) => (parseExponent expChars).map (mant, ·)
  else
    match splitLast isSignChar cs with
    | none => some (cs, 0)
    | some ([], _, _) => some (cs, 0)
    | some (mant, s, expChars) =>
      match mant.getLast? with
      | none => none
      | some c =>
        if isExpChar c then (parseExponent (s :: expChars)).map (mant.dropLast, ·) else none

/-- Remove the point (Malachite's `preprocess_sci_string`, second half): the digit characters
without the point, and the exponent lowered by the number of digits after the point. -/
def splitPoint (cs : List Char) (e : Int) : Option (List Char × Int) :=
  match splitFirst (· == '.') cs with
  | none => some (cs, e)
  | some (intPart, frac) =>
    if frac.head?.any isSignChar then none
    else
      let e' := e - frac.length
      if fitsInt64 e' then some (intPart ++ frac, e') else none

/-- At least one base-`b` digit. -/
def parseMagnitude (b : UInt64) (cs : List Char) : Option AzNat :=
  if cs.isEmpty then none else AzNat.buildFromChars b cs

/-- Malachite's `Integer::parse_int`: an optional single sign, then at least one base-`b`
digit.  The `Bool` is `true` when nonnegative. -/
def parseSignedDigits (b : UInt64) (cs : List Char) : Option (Bool × AzNat) :=
  match cs with
  | [] => none
  | c :: rest =>
    if c == '-' then (parseMagnitude b rest).map (false, ·)
    else if c == '+' then (parseMagnitude b rest).map (true, ·)
    else (parseMagnitude b cs).map (true, ·)

/-- `± n · b^e` as a reduced `AzRat` (`nonneg = true` for `+`).  Zero is returned at once,
so a zero mantissa never raises the base to a large power. -/
def ofSciParts (b : UInt64) (nonneg : Bool) (n : AzNat) (e : Int) : AzRat :=
  if n = 0 then 0
  else
    match e with
    | .ofNat k => ofSignAzNats nonneg (n * b.toAzNat.pow k) 1
    | .negSucc k => ofSignAzNats nonneg n (b.toAzNat.pow (k + 1))

/-- Parse scientific notation in base `b` (`2 ≤ b ≤ 36`, default `10`); see the module
docstring for the accepted language. -/
def fromSci (s : String) (b : UInt64 := 10) : Option AzRat :=
  if b < 2 || 36 < b then none
  else do
    let (mant, e) ← splitExponent b s.toList
    let (digs, e') ← splitPoint mant e
    let (nonneg, n) ← parseSignedDigits b digs
    pure (ofSciParts b nonneg n e')

end Azurite.AzRat
