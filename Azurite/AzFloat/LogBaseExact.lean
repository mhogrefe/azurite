/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.RoundToInteger
import Azurite.AzNat.LogBase
import Azurite.AzNat.RootInt
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.TrailingZeros
import Azurite.AzRat.Construct
import Azurite.AzRat.LogBase

/-!
# When `log_b x` is rational

For a base `b ≥ 2` that is not a power of two and a positive float `x`, `log_b x` is rational
exactly when `x` is a positive integer `c^r` for the *primitive root* `c` of `b` (`b = c^s` with
`s` maximal), and then it is `r / s`.  `maxRootBase b` finds `c` and `s` (`s ≤ 63` for a
64-bit base, by trying the perfect-power tests downward), and `logBaseExact? x b` returns the
rational `r / s` when `x` is such an integer and `none` otherwise.  For a positive rational `q`,
`log_b q` is rational exactly when `q = c^r` for an integer `r` (possibly negative), and
`logBaseExactRat? q b` returns `r / s` then (`AzRat.checkedLogBaseAbs` with the base `c`).
For `log_b (1 + x)`, `logBaseP1Exact? x b` returns `r / s` when `x` is a positive integer with
`1 + x = c^r` (a non-integer `x` never gives a rational `log_b (1 + x)` for such a base).
`Equiv/LogBaseExact.lean` proves the values and, for `none`, the irrationality of the logarithm.
-/

namespace Azurite.AzFloat

/-- The largest `s ∈ [2, t]` with `b` a perfect `s`-th power, or `1`. -/
def maxPowExp (b : AzNat) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | s + 2 => if b.isPow (s + 2) then s + 2 else maxPowExp b (s + 1)

/-- The primitive root of a base `b` whose perfect-power exponents are at most `t`: `b = c^s` with
`s ≤ t` maximal. -/
def maxRootBaseBounded (b : AzNat) (t : ℕ) : AzNat × ℕ :=
  let s := maxPowExp b t
  (if s = 1 then b else b.rootInt s, s)

/-- The primitive root of a 64-bit base: `b = c^s` with `s ≤ 63` maximal. -/
def maxRootBase (b : AzNat) : AzNat × ℕ := maxRootBaseBounded b 63

/-- `log_b x` as a rational when `x` is a positive integer power `c^r` of the primitive root `c`
of `b` (`r / s` for `b = c^s`), `none` otherwise. -/
def logBaseExact? (x : AzFloat) (b : AzNat) : Option AzRat :=
  match x.toAzRat? with
  | some q =>
    if q.sign = true ∧ q.den = 1 ∧ q.num ≠ 0 then
      let cs := maxRootBase b
      (AzNat.checkedLogBase cs.1 q.num).map fun r =>
        AzRat.ofAzInts (AzNat.ofNat r).toAzInt (AzNat.ofNat cs.2).toAzInt
    else none
  | none => none

/-- `some (r / s)` when `q = c^r` for the primitive root `c` of `b = c^s` and an integer `r`,
`none` otherwise. -/
def logBaseExactRat? (q : AzRat) (b : AzNat) : Option AzRat :=
  let cs := maxRootBase b
  (AzRat.checkedLogBaseAbs (UInt64.ofNat cs.1.toNat) q).map fun r =>
    AzRat.ofAzInts (AzInt.ofInt r) (AzNat.ofNat cs.2).toAzInt

/-- `some (r / s)` when `x` is a positive integer with `1 + x = c^r` for the primitive root `c`
of `b = c^s`, `none` otherwise (the integer test comes first, so non-integers cost nothing). -/
def logBaseP1Exact? (x : AzFloat) (b : AzNat) : Option AzRat :=
  if x.isInteger then
    match x.toAzRat? with
    | some q =>
      if q.sign = true ∧ q.den = 1 ∧ q.num ≠ 0 then
        let cs := maxRootBase b
        (AzNat.checkedLogBase cs.1 (q.num + 1)).map fun r =>
          AzRat.ofAzInts (AzNat.ofNat r).toAzInt (AzNat.ofNat cs.2).toAzInt
      else none
    | none => none
  else none

/-! ### A float base -/

/-- The 2-adic valuation of a nonzero `AzNat`. -/
def twoAdic (m : AzNat) : ℕ := m.trailingZeros.getD 0

/-- The odd part of a nonzero `AzNat`: `m = 2^(twoAdic m) · oddPart m`. -/
def oddPart (m : AzNat) : AzNat := m >>> twoAdic m

/-- The dyadic exponent of a finite float `o · 2^i` of exponent `e` and significand `m`:
`i = e − size m + twoAdic m`. -/
def dyadicExp (e : AzInt) (m : AzNat) : AzInt :=
  e - (AzNat.ofNat (m.size - twoAdic m)).toAzInt

/-- `some (log_b x)` when it is rational, for `x = o · 2^i` and `b = s · 2^j` with `o`, `s` odd
and `b ≠ 1`.  For `j = 0` (`b = s` an odd integer) `x` must be an integer power of the
primitive root of `s`; otherwise the value can only be `i / j`, and with `a / e` that fraction
in lowest terms, `x^e = b^a` is checked through the perfect-power tests (`o = c^a` and `s = c^e`
for a common `c` when `a > 0`, and `o = s = 1` when `a < 0`). -/
def logBaseFloatExact? (i : AzInt) (o : AzNat) (j : AzInt) (s : AzNat) : Option AzRat :=
  if j = 0 then
    if i = 0 then
      let cs := maxRootBaseBounded s s.size
      (AzNat.checkedLogBase cs.1 o).map fun r =>
        AzRat.ofAzInts (AzNat.ofNat r).toAzInt (AzNat.ofNat cs.2).toAzInt
    else none
  else
    let r := AzRat.ofAzInts i j
    let a := r.num.toNat
    let e := r.den.toNat
    if r.sign then
      if s.isPow e ∧ o.isPow a ∧ s.rootInt e = o.rootInt a then some r else none
    else if o = 1 ∧ s = 1 then some r else none

end Azurite.AzFloat
