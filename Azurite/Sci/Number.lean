/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Sci.Options
import Azurite.AzNat.ToStringBase
import Mathlib.Algebra.Field.Rat

/-!
# `SciNumber`: a rounded value in positional form, and its rendering

The intermediate structure of `toSci` (`docs/to_sci_plan.md`).  A `SciNumber` is a sign, a
base, the base-`b` digits of a natural number `n` (most significant first, no leading zero;
the empty array is zero) and a `scale`; its value is `± n · b^(−scale)`.  The exponent of the
leading digit is derived: `exponent = digits.size − 1 − scale`.

`SciNumber.value : ℚ` is the specification the first-stage proofs talk about;
`SciNumber.toChars` is the second stage — pure digit shuffling, no arithmetic.
-/

namespace Azurite

/-- A rounded value `± n · base^(−scale)`, with the base-`base` digits of `n` most significant
first.  `digits = #[]` is zero; then `scale` only says how many zeros after the point to print
when trailing zeros are requested. -/
structure SciNumber where
  /-- The sign (`false` for zero). -/
  negative : Bool
  /-- The digit base, `2 ≤ base ≤ 36`. -/
  base : UInt64
  /-- Base-`base` digits, most significant first, no leading zero. -/
  digits : Array UInt64
  /-- The value is `± n · base^(−scale)`, with `n` the number the digits spell. -/
  scale : Int
  deriving DecidableEq, Repr

namespace SciNumber

/-- The number the digits spell, by Horner's rule. -/
def mantissa (x : SciNumber) : Nat :=
  x.digits.foldl (fun acc d => acc * x.base.toNat + d.toNat) 0

/-- The exponent of the leading digit: `digits.size − 1 − scale`. -/
def exponent (x : SciNumber) : Int :=
  (x.digits.size : Int) - 1 - x.scale

/-- The exact value `± mantissa · base^(−scale)` in `ℚ` (the specification). -/
def value (x : SciNumber) : ℚ :=
  (if x.negative then -1 else 1) * (x.mantissa : ℚ) * ((x.base.toNat : ℚ) ^ (-x.scale))

/-- Drop the trailing `'0'`s of a digit list. -/
def dropTrailingZeros (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '0')).reverse

/-- Drop trailing `'0'`s, but only among the last `k` characters (the digits after the point). -/
def dropTrailingZerosWithin (k : Nat) (cs : List Char) : List Char :=
  let n := cs.length
  let keep := n - k
  cs.take keep ++ dropTrailingZeros (cs.drop keep)

/-- The exponent suffix: `e`/`E`, an optional `+`, the exponent in decimal. -/
def exponentChars (fmt : SciFormat) (base : UInt64) (e : Int) : List Char :=
  (if fmt.eLowercase then 'e' else 'E')
    :: ((if 0 < e && (fmt.forceExponentPlusSign || 15 ≤ base) then ['+'] else [])
      ++ (toString e).toList)

/-- Render a `SciNumber` (Malachite's `fmt_sci` / `fmt_zero`, textual part only).

* Zero: `"0"` (after the sign, which is set when a negative value rounded to zero), plus
  `"."` and `scale` zeros when `includeTrailingZeros` and `0 < scale`.
* Exponent form, used when `exponent ≤ negExpThreshold` or `scale < 0`: `d.ddd` followed by
  `exponentChars` (trailing zeros of the mantissa trimmed unless `includeTrailingZeros`; a
  single digit gets no point).
* Otherwise, with `scale = 0`: the digits.
* Otherwise, plain form: trailing zeros among the last `scale` digits trimmed unless
  `includeTrailingZeros`; `0.000…` leading zeros when `exponent < 0`, else the point after
  `exponent + 1` digits (and no point when nothing follows it). -/
def toChars (x : SciNumber) (fmt : SciFormat) : List Char :=
  let sign : List Char := if x.negative then ['-'] else []
  if x.digits.isEmpty then
    sign ++ '0' :: (if fmt.includeTrailingZeros && 0 < x.scale then
      '.' :: List.replicate x.scale.toNat '0' else [])
  else
    let e := x.exponent
    let cs : List Char := (x.digits.map fun d => AzNat.digitToChar d (!fmt.lowercase)).toList
    if e ≤ fmt.negExpThreshold || x.scale < 0 then
      let cs := if fmt.includeTrailingZeros then cs else dropTrailingZeros cs
      let body := match cs with
        | [] => []
        | [d] => [d]
        | d :: rest => d :: '.' :: rest
      sign ++ body ++ exponentChars fmt x.base e
    else if x.scale = 0 then
      sign ++ cs
    else
      let cs := if fmt.includeTrailingZeros then cs else dropTrailingZerosWithin x.scale.toNat cs
      if e < 0 then
        sign ++ '0' :: '.' :: (List.replicate (-e - 1).toNat '0' ++ cs)
      else
        let before := e.toNat + 1
        sign ++ (if before < cs.length then cs.take before ++ '.' :: cs.drop before else cs)

/-- `toChars` as a `String`. -/
def toString (x : SciNumber) (fmt : SciFormat) : String :=
  String.ofList (x.toChars fmt)

end SciNumber

end Azurite
