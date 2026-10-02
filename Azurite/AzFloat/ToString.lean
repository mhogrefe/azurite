/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzNat.OfLimbDigits
import Azurite.AzRat.FromSci
import Azurite.AzRat.Mul
import Azurite.AzRat.Pow
import Azurite.AzRat.ToSci
import Azurite.AzRat.Unary

/-!
# Decimal output of an `AzFloat`

`toDecimalString x` is the **shortest round-tripping decimal**: the smallest number `p ≥ 1` of
significant digits such that the exact value of `x`, rounded to nearest at `p` decimal digits
(`AzRat.toSci`), converts back to `x` at `x`'s own precision — then that `p`-digit rendering.
It is lossy by design (the hexadecimal format of `HexString.lean` is the exact one), and it is
not MPFR's or Malachite's rule (those print a digit count that depends on the precision alone).

The predicate "the `p`-digit rounding round-trips" is monotone in `p` (the nearest `p`-digit
decimal is also a `(p+1)`-digit decimal), so `p` is found by a search: an upper bound from
`p ≤ ⌈precision · log₁₀ 2⌉ + 2` (checked, and doubled if it ever failed), then a binary search
below it (`searchLeast`).  Each probe is one `toSci` and one `ofAzRat`.

Layout follows `toSci` with its defaults (exponent notation below `10^-6` or when the digits do
not reach the point, lowercase `e`), with the float convention that the fractional part is never
empty: `1.0`, `0.5`, `1.0e-6`, `1.2676506002282294e30`; the special values are `NaN`, `Infinity`,
`-Infinity` and `0.0`.
-/

namespace Azurite

namespace SciNumber

/-- The value of a `SciNumber` as an `AzRat` (computably; `value` is the specification). -/
def toAzRat (x : SciNumber) : AzRat :=
  let m := (AzNat.ofLimbDigits x.base x.digits.reverse).toAzRat
  let v := m * x.base.toAzRat.zpow (-x.scale)
  if x.negative then -v else v

end SciNumber

namespace AzFloat

/-- The least `p ∈ [lo, hi]` with `pred p = true`, by binary search, assuming `pred hi = true`
and that `pred` is monotone (`hi` if those assumptions fail). -/
def searchLeast (pred : Nat → Bool) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if pred mid then searchLeast pred lo mid else searchLeast pred (mid + 1) hi
  else hi
termination_by hi - lo
decreasing_by all_goals omega

/-- Double `p` until `pred p` holds (at most `fuel` times). -/
def expandUntil (pred : Nat → Bool) (p fuel : Nat) : Nat :=
  match fuel with
  | 0 => p
  | fuel + 1 => if pred p then p else expandUntil pred (2 * p) fuel

/-- The `toSci` options for `p` significant decimal digits, to nearest. -/
def decimalOptions (p : Nat) : SciOptions :=
  { base := 10, mode := .Nearest, size := .precision p, format := {} }

/-- Does rounding `q` (the value of `x`, of precision `P`) to `p` decimal digits round-trip? -/
def decimalRoundTrips (x : AzFloat) (q : AzRat) (P p : Nat) : Bool :=
  match q.toSciNumber (decimalOptions p) with
  | some sn => ofAzRat sn.toAzRat P == x
  | none => false

/-- The shortest round-tripping decimal precision of a finite nonzero float (`0` otherwise). -/
def shortestDecimalPrecision (x : AzFloat) : Nat :=
  match x.toAzRat?, x.precision? with
  | some q, some P =>
    let pred := decimalRoundTrips x q P
    -- `⌈P · log₁₀ 2⌉ + 2` digits always suffice; the doubling only guards the estimate
    let hi := expandUntil pred (P * 30103 / 100000 + 2) 64
    searchLeast pred 1 hi
  | _, _ => 0

/-- Insert `".0"` when there is no point: after the digits, before an exponent marker. -/
def ensurePoint (cs : List Char) : List Char :=
  if cs.contains '.' then cs
  else
    match AzRat.splitFirst (· == 'e') cs with
    | some (mant, rest) => mant ++ '.' :: '0' :: 'e' :: rest
    | none => cs ++ ['.', '0']

/-- The decimal rendering of `x` at `p` significant digits (to nearest), `none` for `NaN`,
`±∞` and `p = 0`. -/
def toDecimalAt (x : AzFloat) (p : Nat) : Option String :=
  match x.toAzRat? with
  | some q => (q.toSci (decimalOptions p)).map fun s => String.ofList (ensurePoint s.toList)
  | none => none

/-- The shortest round-tripping decimal rendering. -/
def toDecimalString (x : AzFloat) : String :=
  match x with
  | nan => "NaN"
  | infinity true => "Infinity"
  | infinity false => "-Infinity"
  | zero => "0.0"
  | finite .. => (toDecimalAt x (shortestDecimalPrecision x)).getD ""

instance : ToString AzFloat := ⟨toDecimalString⟩

end AzFloat

end Azurite
