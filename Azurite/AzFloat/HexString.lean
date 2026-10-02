/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Precision
import Azurite.AzInt.Compare
import Azurite.AzInt.DivMod
import Azurite.AzInt.ShiftLeft
import Azurite.AzNat.LimbDigits
import Azurite.AzNat.ToStringBase
import Azurite.AzRat.FromSci

/-!
# The hexadecimal debug format of `AzFloat`

The format of the author's Malachite `format!("{:#x}", ComparableFloat(x))`: the exact value in
hexadecimal (every float is exactly representable in base `16`), followed by `#` and the
precision, so that the string determines the float.  Examples: `0x1.0#1`, `0x0.8#5` (one half at
precision `5`), `-0x1.8#2`, `0xff.0#8`, `0x4d2.8#12`, `0x0.0050df15a4acf314#53`, `0x6.f70E+25#13`,
`0x1.0E-250000000#1`; the special values are `NaN`, `Infinity`, `-Infinity` and `0x0.0`.

Rules (first principles, matching that implementation): with binary exponent `e` and precision
`p`, the hexadecimal exponent of the leading digit is `E = ⌊(e − 1) / 4⌋`, the leading digit
holds `m' = ((e − 1) mod 4) + 1` significant bits, and the number of digits written is
`D = ⌈(p − m') / 4⌉ + 1` — exactly enough to hold the `p` bits, trailing zeros included.  The
layout is Malachite's `to_sci` in base `16` with `D` digits and threshold `−6`: scientific
`d.ddd E±k` when `E ≤ −6` or `E ≥ D`, otherwise plain with the point after `E + 1` digits (and
`0.00…` leading zeros when `E < 0`); the fractional part is never empty (`ff.0`, `1.0E+25`).

`toHexString` writes the format and `ofHexString` reads it back; `Equiv/HexString.lean` proves
`ofHexString_toHexString : ofHexString (toHexString x) = some x` for every float, with no side
conditions.  The reader is strict: it accepts exactly the strings the writer produces (either
digit case, no `-0x0.0`, no inexact values).
-/

namespace Azurite.AzFloat

/-- Hexadecimal digit characters of `n`, most significant first (empty for `0`). -/
def hexDigits (n : AzNat) (uppercase : Bool) : List Char :=
  ((n.limbDigits 16).reverse.map fun d => AzNat.digitToChar d uppercase).toList

/-- Decimal digit characters of `n`, most significant first (empty for `0`). -/
def decDigits (n : AzNat) : List Char :=
  ((n.limbDigits 10).reverse.map fun d => AzNat.digitToChar d false).toList

/-- The number of hexadecimal digits that exactly hold `p` bits whose leading digit holds `m'`
of them (`1 ≤ m' ≤ 4`). -/
def hexDigitCount (p m' : Nat) : Nat := (p - m' + 3) / 4 + 1

/-- Lay out the hexadecimal digits `ds` (most significant first, the leading one nonzero) of a
value whose leading digit has hexadecimal exponent `E`: scientific when `E ≤ −6` or `E ≥ |ds|`,
plain otherwise; the fractional part is never empty. -/
def hexLayout (ds : List Char) (E : AzInt) : List Char :=
  if E ≤ AzInt.ofInt (-6) ∨ (AzNat.ofNat ds.length).toAzInt ≤ E then
    match ds with
    | [] => []
    | d :: rest =>
      d :: '.' :: (if rest.isEmpty then ['0'] else rest) ++
        'E' :: (if E.sign then '+' else '-') :: decDigits E.abs
  else if E.sign then
    let before := E.abs.toNat + 1
    ds.take before ++ '.' :: (if before < ds.length then ds.drop before else ['0'])
  else
    '0' :: '.' :: (List.replicate (E.abs.toNat - 1) '0' ++ ds)

/-- The hexadecimal debug rendering, as characters. -/
def toHexChars (x : AzFloat) (uppercase : Bool := false) : List Char :=
  match x with
  | nan => "NaN".toList
  | infinity true => "Infinity".toList
  | infinity false => "-Infinity".toList
  | zero => "0x0.0".toList
  | finite s e p m _ =>
    let n := coreSignificand p m
    let em1 := e - 1
    let E := em1.ediv (AzInt.ofInt 4)
    let m' := (em1.emod (AzInt.ofInt 4)).abs.toNat + 1
    let D := hexDigitCount p m'
    let N := n.shiftLeft (4 * (D - 1) + m' - p)
    (if s then [] else ['-']) ++ '0' :: 'x' :: hexLayout (hexDigits N uppercase) E ++
      '#' :: Nat.toDigits 10 p

/-- The hexadecimal debug rendering (Malachite's `{:#x}` of a `ComparableFloat`). -/
def toHexString (x : AzFloat) (uppercase : Bool := false) : String :=
  String.ofList (toHexChars x uppercase)

/-- Split off a hexadecimal exponent `E±ddd` (the last sign in the string, which must follow
an `E`); `(cs, 0)` when there is none. -/
def splitHexExponent (cs : List Char) : Option (List Char × AzInt) :=
  match AzRat.splitLast AzRat.isSignChar cs with
  | none => some (cs, 0)
  | some (bef, s, aft) =>
    match bef.getLast? with
    | none => none
    | some c =>
      if AzRat.isExpChar c then
        (AzRat.parseMagnitude 10 aft).map fun n => (bef.dropLast, AzInt.mkNorm (s == '+') n)
      else none

/-- Read the hexadecimal debug format; `none` for anything the writer would not produce. -/
def ofHexChars (cs : List Char) : Option AzFloat :=
  if cs = "NaN".toList then some nan
  else if cs = "Infinity".toList then some (infinity true)
  else if cs = "-Infinity".toList then some (infinity false)
  else
    let (neg, cs) := if cs.head? = some '-' then (true, cs.tail) else (false, cs)
    match cs with
    | '0' :: 'x' :: body =>
      if body = "0.0".toList then (if neg then none else some zero)
      else do
        let (mant, precChars) ← AzRat.splitFirst (· == '#') body
        let p ← AzRat.parseDecimalDigits precChars
        let (digitsPart, E) ← splitHexExponent mant
        let (intPart, frac) ← AzRat.splitFirst (· == '.') digitsPart
        let N ← AzRat.parseMagnitude 16 (intPart ++ frac)
        if p = 0 ∨ N = 0 then none
        else
          let sh := N.size - p
          if N.isMultipleOfPow2 sh then
            let ex := (AzNat.ofNat N.size).toAzInt +
              (E - (AzNat.ofNat frac.length).toAzInt).shiftLeft 2
            some (mkFinite (!neg) ex p (N.shiftRight sh))
          else none
    | _ => none

/-- Read the hexadecimal debug format from a string. -/
def ofHexString (s : String) : Option AzFloat := ofHexChars s.toList

end Azurite.AzFloat
