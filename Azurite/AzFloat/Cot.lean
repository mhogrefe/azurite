/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CotBracket

/-!
## The cotangent

`cot x = cos x / sin x`, correctly rounded to precision `p` in every mode with the comparison
against the exact value:

* `cotPrecRound x p mode`, `cot x` — a float `x`;
* `cotRatPrecRound q p mode`, `cotRat q p` — an `AzRat` `q`;
* `cotWithPeriodPrecRound x u p mode`, `cotWithPeriod x u` — `cot (2π x / u)` for a float `x`
  and a `UInt64` period `u`; `cotRatWithPeriodPrecRound q u p mode`, `cotRatWithPeriod q u p`
  for an `AzRat` `q`;
* `cotPiPrecRound`, `cotPi`, `cotPiRatPrecRound`, `cotPiRat` — `cot (π x)`, the period-`2` cases.

Each is a certified Ziv loop (`zivLoopCertified`, no fuel) on the quotient of the cosine bracket
by the sine bracket of one joint evaluation (`AzFloat/CotBracket.lean`), preceded by a
tiny-argument test (`cotTinyCore?`: `1/a − a ≤ cot a < 1/a`).

**Poles.**  The cotangent is the quotient of the cosine by the sine, and at a pole the sine is a
zero carrying the sign of the argument (the convention of the cosecant), so the result is the
infinity with the sign of the argument **times the sign of the cosine**; this is also the
reciprocal of IEEE 754's `tanPi`, whose zeros are `+0` at the even and `−0` at the odd positive
integers.  Hence `cot 0 = +∞` (the zero of AzFloat is unsigned), exactly, at every precision,
and with a period, after the exact reduction to `r ∈ [0, 1)`, `cotPeriodCore` decides by the
reduced denominator of `r` (Niven's theorem for the tangent):

* `1` (`x/u` an integer, `cos = 1`): exactly `±∞` with the sign of `x`;
* `2` (`x/u` a half-integer, `cos = −1`): exactly `∓∞`, the sign opposite to that of `x`;
* `4`: exactly `0`; `8`: exactly `±1`;
* otherwise the value is irrational and the loop runs.

A nonzero float or rational is never a pole of `cot` itself (`sin x` is irrational).

Special values: `u = 0` gives `NaN`; `cot NaN = cot (±∞) = NaN`; `p = 0` gives `NaN` unless the
argument is `0`.
-/

namespace Azurite.AzFloat

/-- `cot x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`+∞` for `x = 0`; `(nan, .eq)` for `p = 0` otherwise). -/
def cotPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (infinity true, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match cotTiny? s (finite s e q m hv) e p mode with
      | some r => r
      | none =>
        zivLoopCertified (cotApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
          (cotApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
            (finiteVal_ne_zero s e hv) (abs_finiteVal_bounds s e hv).2 (p + zivGuardBits)
            (by unfold zivGuardBits; omega))

/-- `cot x` rounded to nearest at the precision of `x`. -/
def cot (x : AzFloat) : AzFloat := (cotPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `cot q` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value (`+∞` for `q = 0`; `(nan, .eq)` for `p = 0` otherwise). -/
def cotRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (infinity true, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match cotTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (cotRatApprox q) p mode (p + zivGuardBits)
        (cotRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `cot q` rounded to nearest at precision `p`. -/
def cotRat (q : AzRat) (p : Nat) : AzFloat := (cotRatPrecRound q p .Nearest).1

/-- `± cot (2πr)` for a reduced rational `r ∈ [0, 1)` (`neg`: the sign is negative), rounded to
precision `p` with `mode`: the signed infinities for the denominators `1` and `2` (the poles:
`cos = 1` and `cos = −1`), `0` for `4`, `±1` for `8`, and otherwise the certified Ziv loop. -/
def cotPeriodCore (neg : Bool) (r : AzRat)
    (hr : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ) ∧ ((AzRat.toRat r : ℚ) : ℝ) < 1) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  if h1 : r.den = AzNat.ofNat 1 then (infinity (!neg), .eq)
  else if h2 : r.den = AzNat.ofNat 2 then (infinity neg, .eq)
  else if h4 : r.den = AzNat.ofNat 4 then (zero, .eq)
  else if h8 : r.den = AzNat.ofNat 8 then
    setPrecRound (signedPow2
      (neg != decide (r.num = AzNat.ofNat 1 ∨ r.num = AzNat.ofNat 5)) 0) p mode
  else
    zivLoopCertified (cotPeriodApprox neg r) p mode (p + zivGuardBits)
      (cotPeriodApprox_isSome_exists p mode neg r hr.1 hr.2 h1 h2 h4 h8 (p + zivGuardBits)
        (by unfold zivGuardBits; omega))

/-- `cot (2π x / u)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `u = 0`; `+∞` for `x = 0`; `(nan, .eq)` for `p = 0` otherwise); a signed
infinity at the poles. -/
def cotWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
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
        match cotPeriodTiny? (!s) m (AzNat.ofNat u.toNat) (e - (AzNat.ofNat m.size).toAzInt)
          (e + AzInt.ofInt 3) p mode with
        | some r => r
        | none =>
          cotPeriodCore (!s)
            (periodFrac m (e - (AzNat.ofNat m.size).toAzInt) (AzNat.ofNat u.toNat)) (by
              obtain ⟨_, _, hr0, hr1⟩ :=
                periodFrac_spec m (e - (AzNat.ofNat m.size).toAzInt) hun
              exact ⟨hr0, hr1⟩) p mode

/-- `cot (2π x / u)` rounded to nearest at the precision of `x`. -/
def cotWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (cotWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

/-- `cot (2π q / u)` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the
comparison with the exact value (`(nan, .eq)` for `u = 0`; `+∞` for `q = 0`; `(nan, .eq)` for
`p = 0` otherwise); a signed infinity at the poles. -/
def cotRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hu : u.toNat = 0 then (nan, .eq)
  else if h0 : q.num = 0 then (infinity true, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
      rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
    match cotPeriodTiny? (!q.sign) q.num (q.den * AzNat.ofNat u.toNat) (AzInt.ofInt 0)
      (ratExpBound q + AzInt.ofInt 2) p mode with
    | some r => r
    | none =>
      cotPeriodCore (!q.sign) (periodFracRat q (AzNat.ofNat u.toNat)) (by
        obtain ⟨_, _, hr0, hr1⟩ := periodFracRat_spec q hun
        exact ⟨hr0, hr1⟩) p mode

/-- `cot (2π q / u)` rounded to nearest at precision `p`. -/
def cotRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (cotRatWithPeriodPrecRound q u p .Nearest).1

/-- `cot (π x)` rounded to precision `p` with `mode`, and the comparison with the exact value;
a signed infinity at the integers (`+∞` at `0`). -/
def cotPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  cotWithPeriodPrecRound x 2 p mode

/-- `cot (π x)` rounded to nearest at the precision of `x`. -/
def cotPi (x : AzFloat) : AzFloat := (cotPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `cot (π q)` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value; a signed infinity at the integers (`+∞` at `0`). -/
def cotPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  cotRatWithPeriodPrecRound q 2 p mode

/-- `cot (π q)` rounded to nearest at precision `p`. -/
def cotPiRat (q : AzRat) (p : Nat) : AzFloat := (cotPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
