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

/-- The odd part and dyadic exponent of `1 + x` for a float `x = ±o · 2^i > −1` of sign `s`:
`1 + x = o' · 2^i'`.  For `x ≥ 0` with `i ≥ 0` the sum is the integer `o · 2^i + 1`; otherwise
`1 + x = (2^t ± o) / 2^t` with `t = −i`. -/
def onePlusDyadic (s : Bool) (i : AzInt) (o : AzNat) : AzNat × AzInt :=
  if s then
    if i.sign then
      let n := (o <<< i.abs.toNat) + 1
      (oddPart n, (AzNat.ofNat (twoAdic n)).toAzInt)
    else
      let u := ((1 : AzNat) <<< i.abs.toNat) + o
      (oddPart u, (AzNat.ofNat (twoAdic u)).toAzInt - (AzNat.ofNat i.abs.toNat).toAzInt)
  else
    let u := ((1 : AzNat) <<< i.abs.toNat) - o
    (oddPart u, (AzNat.ofNat (twoAdic u)).toAzInt - (AzNat.ofNat i.abs.toNat).toAzInt)

/-- The dyadic exponent of a rational: `twoAdic num − twoAdic den`. -/
def ratDyadicExp (q : AzRat) : AzInt :=
  (AzNat.ofNat (twoAdic q.num)).toAzInt - (AzNat.ofNat (twoAdic q.den)).toAzInt

/-- `some (log_b q)` when it is rational, for `q = (n / d) · 2^i` with `n`, `d` odd and coprime
and `b = s · 2^j`: only possible with `d = 1` (the float case on `n · 2^i`) or `n = 1` (the float
case on `d · 2^(−i)`, negated). -/
def logBaseRatFloatExact? (i : AzInt) (n d : AzNat) (j : AzInt) (s : AzNat) : Option AzRat :=
  if d = 1 then logBaseFloatExact? i n j s
  else if n = 1 then (logBaseFloatExact? (-i) d j s).map fun r => -r
  else none

/-- `some (log_b x)` when it is rational, for `x = o · 2^i` and `b = (n / d) · 2^j` with `n`, `d`
odd and coprime: only possible with `d = 1` (the float case with base `n · 2^j`) or `n = 1` (the
float case with base `d · 2^(−j)`, negated). -/
def logBaseRatBaseExact? (i : AzInt) (o : AzNat) (j : AzInt) (n d : AzNat) : Option AzRat :=
  if d = 1 then logBaseFloatExact? i o j n
  else if n = 1 then (logBaseFloatExact? i o (-j) d).map fun r => -r
  else none

/-- `some (log_{n₂} n₁)` when rational, for odd integers `n₁`, `n₂ ≥ 3` (the odd-integer-base
case of `logBaseFloatExact?`). -/
def logOddExact? (n₁ n₂ : AzNat) : Option AzRat := logBaseFloatExact? 0 n₁ 0 n₂

/-- The common value of `log_{n₂} n₁` and `log_{d₂} d₁` when both are rational and equal. -/
def logOddPairExact? (n₁ d₁ n₂ d₂ : AzNat) : Option AzRat :=
  match logOddExact? n₁ n₂, logOddExact? d₁ d₂ with
  | some v₁, some v₂ => if v₁ = v₂ then some v₁ else none
  | _, _ => none

/-- The 2-adic consistency of a candidate value `v` of `log_b q` with the dyadic exponents `i`
of `q` and `j` of `b`: `i = 0` when `j = 0`, and `v = i / j` otherwise. -/
def dyadicOK (i j : AzInt) (v : AzRat) : Bool :=
  if j = 0 then decide (i = 0) else decide (v = AzRat.ofAzInts i j)

/-- The negative candidate: `−u` when `log_{d₂} n₁ = log_{n₂} d₁ = u` is 2-adically consistent. -/
def logBaseRatRatNeg? (i : AzInt) (n₁ d₁ : AzNat) (j : AzInt) (n₂ d₂ : AzNat) : Option AzRat :=
  match logOddPairExact? n₁ d₁ d₂ n₂ with
  | some u => if dyadicOK i j (-u) then some (-u) else none
  | none => none

/-- `some (log_b q)` when it is rational, for `q = (n₁ / d₁) · 2^i` and `b = (n₂ / d₂) · 2^j`
with odd coprime pairs.  When one of `d₂`, `n₂`, `d₁`, `n₁` is `1` this is a float-base or
float-argument case; otherwise `log_b q = a/e` forces `log_{n₂} n₁ = log_{d₂} d₁ = a/e`
(for `a ≥ 0`) or `log_{d₂} n₁ = log_{n₂} d₁ = −a/e` (for `a < 0`), together with the 2-adic
condition `i e = j a` (`dyadicOK`). -/
def logBaseRatRatExact? (i : AzInt) (n₁ d₁ : AzNat) (j : AzInt) (n₂ d₂ : AzNat) :
    Option AzRat :=
  if d₂ = 1 then logBaseRatFloatExact? i n₁ d₁ j n₂
  else if n₂ = 1 then (logBaseRatFloatExact? i n₁ d₁ (-j) d₂).map fun r => -r
  else if d₁ = 1 then logBaseRatBaseExact? i n₁ j n₂ d₂
  else if n₁ = 1 then (logBaseRatBaseExact? (-i) d₁ j n₂ d₂).map fun r => -r
  else
    match logOddPairExact? n₁ d₁ n₂ d₂ with
    | some v => if dyadicOK i j v then some v else logBaseRatRatNeg? i n₁ d₁ j n₂ d₂
    | none => logBaseRatRatNeg? i n₁ d₁ j n₂ d₂

end Azurite.AzFloat
