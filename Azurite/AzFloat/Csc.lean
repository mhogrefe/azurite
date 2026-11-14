/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CscBracket

/-!
## The cosecant

`csc x = 1 / sin x`, correctly rounded to precision `p` in every mode with the comparison against
the exact value:

* `cscPrecRound x p mode`, `csc x` — a float `x`;
* `cscRatPrecRound q p mode`, `cscRat q p` — an `AzRat` `q`;
* `cscWithPeriodPrecRound x u p mode`, `cscWithPeriod x u` — `csc (2π x / u)` for a float `x`
  and a `UInt64` period `u`; `cscRatWithPeriodPrecRound q u p mode`, `cscRatWithPeriod q u p`
  for an `AzRat` `q`;
* `cscPiPrecRound`, `cscPi`, `cscPiRatPrecRound`, `cscPiRat` — `csc (π x)`, the period-`2` cases.

Each is a certified Ziv loop (`zivLoopCertified`, no fuel) on the reciprocal of a sine bracket
(`AzFloat/CscBracket.lean`), preceded by a tiny-argument test (`cscTinyCore?`:
`1/a < csc a ≤ 1/a + a`), since next to `0` the cosecant is large and the sine bracket would
need about `|e|` extra bits.

**Poles.**  `csc 0 = +∞` (the zero of AzFloat is unsigned), exactly, at every precision.  With a
period, the argument is reduced exactly to `r ∈ [0, 1)` and `cscPeriodCore` decides by the
reduced denominator of `r` (Niven's theorem for the sine):

* `1, 2` (`x/u` a multiple of `1/2`): a pole; the result is exactly `±∞` **with the sign of
  `x`** — the sine there is a zero carrying that sign, and the cosecant is its reciprocal, which
  keeps the function odd;
* `4`: exactly `±1`; `12`: exactly `±2`;
* otherwise the value is irrational and the loop runs.

A nonzero float or rational is never a pole of `csc` itself (`sin x` is irrational).

Special values: `u = 0` gives `NaN`; `csc NaN = csc (±∞) = NaN`; `p = 0` gives `NaN` unless the
argument is `0`.
-/

namespace Azurite.AzFloat

/-- `csc x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`+∞` for `x = 0`; `(nan, .eq)` for `p = 0` otherwise). -/
def cscPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (infinity true, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match cscTiny? s (finite s e q m hv) e p mode with
      | some r => r
      | none =>
        zivLoopCertified (cscApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
          (cscApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
            (finiteVal_ne_zero s e hv) (abs_finiteVal_bounds s e hv).2 (p + zivGuardBits)
            (by unfold zivGuardBits; omega))

/-- `csc x` rounded to nearest at the precision of `x`. -/
def csc (x : AzFloat) : AzFloat := (cscPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `csc q` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value (`+∞` for `q = 0`; `(nan, .eq)` for `p = 0` otherwise). -/
def cscRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (infinity true, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match cscTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (cscRatApprox q) p mode (p + zivGuardBits)
        (cscRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `csc q` rounded to nearest at precision `p`. -/
def cscRat (q : AzRat) (p : Nat) : AzFloat := (cscRatPrecRound q p .Nearest).1

/-- `± csc (2πr)` for a reduced rational `r ∈ [0, 1)` (`neg`: the sign is negative), rounded to
precision `p` with `mode`: the signed infinity for the denominators `1, 2` (the poles), `±1` for
`4`, `±2` for `12`, and otherwise the certified Ziv loop. -/
def cscPeriodCore (neg : Bool) (r : AzRat)
    (hr : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ) ∧ ((AzRat.toRat r : ℚ) : ℝ) < 1) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  if h1 : r.den = AzNat.ofNat 1 then (infinity (!neg), .eq)
  else if h2 : r.den = AzNat.ofNat 2 then (infinity (!neg), .eq)
  else if h4 : r.den = AzNat.ofNat 4 then
    setPrecRound (signedPow2 (neg != decide (r.num = AzNat.ofNat 1)) 0) p mode
  else if h12 : r.den = AzNat.ofNat 12 then
    setPrecRound (signedPow2
      (neg != decide (r.num = AzNat.ofNat 1 ∨ r.num = AzNat.ofNat 5)) 1) p mode
  else
    zivLoopCertified (cscPeriodApprox neg r) p mode (p + zivGuardBits)
      (cscPeriodApprox_isSome_exists p mode neg r hr.1 hr.2 h1 h2 h4 h12 (p + zivGuardBits)
        (by unfold zivGuardBits; omega))

/-- `csc (2π x / u)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `u = 0`; `+∞` for `x = 0`; `(nan, .eq)` for `p = 0` otherwise); `±∞`
with the sign of `x` at the poles. -/
def cscWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hu : u.toNat = 0 then (nan, .eq)
  else
    match x with
    | nan => (nan, .eq)
    | infinity _ => (nan, .eq)
    | zero => (infinity true, .eq)
    | finite s e _ m _ =>
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
          rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
        match cscPeriodTiny? (!s) m (AzNat.ofNat u.toNat) (e - (AzNat.ofNat m.size).toAzInt)
          (e + AzInt.ofInt 3) p mode with
        | some r => r
        | none =>
          cscPeriodCore (!s)
            (periodFrac m (e - (AzNat.ofNat m.size).toAzInt) (AzNat.ofNat u.toNat)) (by
              obtain ⟨_, _, hr0, hr1⟩ :=
                periodFrac_spec m (e - (AzNat.ofNat m.size).toAzInt) hun
              exact ⟨hr0, hr1⟩) p mode

/-- `csc (2π x / u)` rounded to nearest at the precision of `x`. -/
def cscWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (cscWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

/-- `csc (2π q / u)` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the
comparison with the exact value (`(nan, .eq)` for `u = 0`; `+∞` for `q = 0`; `(nan, .eq)` for
`p = 0` otherwise); `±∞` with the sign of `q` at the poles. -/
def cscRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hu : u.toNat = 0 then (nan, .eq)
  else if h0 : q.num = 0 then (infinity true, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
      rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
    match cscPeriodTiny? (!q.sign) q.num (q.den * AzNat.ofNat u.toNat) (AzInt.ofInt 0)
      (ratExpBound q + AzInt.ofInt 2) p mode with
    | some r => r
    | none =>
      cscPeriodCore (!q.sign) (periodFracRat q (AzNat.ofNat u.toNat)) (by
        obtain ⟨_, _, hr0, hr1⟩ := periodFracRat_spec q hun
        exact ⟨hr0, hr1⟩) p mode

/-- `csc (2π q / u)` rounded to nearest at precision `p`. -/
def cscRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (cscRatWithPeriodPrecRound q u p .Nearest).1

/-- `csc (π x)` rounded to precision `p` with `mode`, and the comparison with the exact value;
`±∞` with the sign of `x` at the integers (`+∞` at `0`). -/
def cscPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  cscWithPeriodPrecRound x 2 p mode

/-- `csc (π x)` rounded to nearest at the precision of `x`. -/
def cscPi (x : AzFloat) : AzFloat := (cscPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `csc (π q)` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value; `±∞` with the sign of `q` at the integers (`+∞` at `0`). -/
def cscPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  cscRatWithPeriodPrecRound q 2 p mode

/-- `csc (π q)` rounded to nearest at precision `p`. -/
def cscPiRat (q : AzRat) (p : Nat) : AzFloat := (cscPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
