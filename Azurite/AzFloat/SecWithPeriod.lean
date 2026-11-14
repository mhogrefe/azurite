/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SecWithPeriodBracket

/-!
## The secant with a period: `sec (2π x / u)`, and the secant of a rational

`secWithPeriodPrecRound x u p mode` is `sec (2π x / u)` for a float `x` and a `UInt64` period
`u` (degrees for `u = 360`, turns for `u = 1`), correctly rounded to precision `p` in `mode`, with
the comparison against the exact value; `secWithPeriod x u` rounds to nearest at the precision
of `x`.  `secRatWithPeriodPrecRound q u p mode`, `secRatWithPeriod q u p` are the same for an
`AzRat` `q`, and `secRatPrecRound q p mode`, `secRat q p` are `sec q` for a rational `q`
(no period).

The argument is reduced exactly: `|x|/u` has the fractional part `r ∈ [0, 1)` as a reduced
rational (`periodFrac`, `periodFracRat`), and `sec (2π x / u) = sec (2πr)`.  `secPeriodCore`
decides by the reduced denominator of `r` (Niven's theorem for the cosine):

* `1` (`x/u` an even multiple of `1/2`): exactly `1`; `2` (an odd multiple): exactly `−1`;
* `4` (`x/u` an odd multiple of `1/4`): **a pole; the result is exactly `+∞`** — the cosine is
  the (unsigned) zero at every such point, and the secant is its reciprocal;
* `3`: exactly `−2`; `6`: exactly `2`;
* otherwise the value is irrational (e.g. `±√2` at the odd multiples of `1/8`), and the
  certified Ziv loop runs on `secPeriodApprox r` (`AzFloat/SecWithPeriodBracket.lean`).

Tiny arguments are rounded by `secTiny?` before any reduction.

Special values: `u = 0` or `p = 0` give `NaN`; `sec NaN = sec (±∞) = NaN`; `x = 0` gives `1`.
-/

namespace Azurite.AzFloat

/-- `sec (2πr)` for a reduced rational `r ∈ [0, 1)`, rounded to precision `p` with `mode`:
`1`, `−1`, `+∞` (the pole), `−2`, `2` for the denominators `1, 2, 4, 3, 6`, and otherwise the
certified Ziv loop. -/
def secPeriodCore (r : AzRat)
    (hr : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ) ∧ ((AzRat.toRat r : ℚ) : ℝ) < 1) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  if h1 : r.den = AzNat.ofNat 1 then setPrecRound one p mode
  else if h2 : r.den = AzNat.ofNat 2 then setPrecRound (-one) p mode
  else if h4 : r.den = AzNat.ofNat 4 then (infinity true, .eq)
  else if h3 : r.den = AzNat.ofNat 3 then setPrecRound (-(one <<< AzInt.ofInt 1)) p mode
  else if h6 : r.den = AzNat.ofNat 6 then setPrecRound (one <<< AzInt.ofInt 1) p mode
  else
    zivLoopCertified (secPeriodApprox r) p mode (p + zivGuardBits)
      (secPeriodApprox_isSome_exists p mode r hr.1 hr.2 h1 h2 h3 h4 h6 (p + zivGuardBits)
        (by unfold zivGuardBits; omega))

/-- `sec (2π x / u)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `p = 0` or `u = 0`); `+∞` at the poles. -/
def secWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hu : u.toNat = 0 then (nan, .eq)
  else
    match x with
    | nan => (nan, .eq)
    | infinity _ => (nan, .eq)
    | zero => if p = 0 then (nan, .eq) else setPrecRound one p mode
    | finite _ e _ m _ =>
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
          rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
        match secTiny? (e + AzInt.ofInt 3) p mode with
        | some r => r
        | none =>
          secPeriodCore (periodFrac m (e - (AzNat.ofNat m.size).toAzInt) (AzNat.ofNat u.toNat))
            (by
              obtain ⟨_, _, hr0, hr1⟩ :=
                periodFrac_spec m (e - (AzNat.ofNat m.size).toAzInt) hun
              exact ⟨hr0, hr1⟩) p mode

/-- `sec (2π x / u)` rounded to nearest at the precision of `x`. -/
def secWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (secWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

/-- `sec (2π q / u)` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the
comparison with the exact value (`(nan, .eq)` for `p = 0` or `u = 0`); `+∞` at the poles. -/
def secRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hu : u.toNat = 0 then (nan, .eq)
  else if hp : p = 0 then (nan, .eq)
  else if h0 : q.num = 0 then setPrecRound one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
      rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
    match secTiny? (ratExpBound q + AzInt.ofInt 2) p mode with
    | some r => r
    | none =>
      secPeriodCore (periodFracRat q (AzNat.ofNat u.toNat)) (by
        obtain ⟨_, _, hr0, hr1⟩ := periodFracRat_spec q hun
        exact ⟨hr0, hr1⟩) p mode

/-- `sec (2π q / u)` rounded to nearest at precision `p`. -/
def secRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (secRatWithPeriodPrecRound q u p .Nearest).1

/-- `sec q` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value (`(nan, .eq)` for `p = 0`). -/
def secRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else if h0 : q.num = 0 then setPrecRound one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    match secTiny? (ratExpBound q) p mode with
    | some r => r
    | none =>
      zivLoopCertified (secRatApprox q) p mode (p + zivGuardBits)
        (secRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `sec q` rounded to nearest at precision `p`. -/
def secRat (q : AzRat) (p : Nat) : AzFloat := (secRatPrecRound q p .Nearest).1

/-- `sec (π x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`); `+∞` at the half-integers. -/
def secPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  secWithPeriodPrecRound x 2 p mode

/-- `sec (π x)` rounded to nearest at the precision of `x`. -/
def secPi (x : AzFloat) : AzFloat := (secPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `sec (π q)` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value (`(nan, .eq)` for `p = 0`); `+∞` at the half-integers. -/
def secPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  secRatWithPeriodPrecRound q 2 p mode

/-- `sec (π q)` rounded to nearest at precision `p`. -/
def secPiRat (q : AzRat) (p : Nat) : AzFloat := (secPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
