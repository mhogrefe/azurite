/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.TanWithPeriodBracket

/-!
## The tangent with a period: `tan (2π x / u)`

`tanWithPeriodPrecRound x u p mode` is `tan (2π x / u)` for a float `x` and a `UInt64` period
`u` (degrees for `u = 360`, turns for `u = 1`), correctly rounded to precision `p` in `mode`, with
the comparison against the exact value; `tanWithPeriod x u` rounds to nearest at the precision
of `x`.

The argument is reduced exactly: `|x|/u = m 2^E / u` has the fractional part
`r = periodFrac m E u ∈ [0, 1)` as a reduced rational, and
`tan (2π x / u) = ± tan (2πr)` with the sign of `x`.  By Niven's theorem for the tangent
(`Transcendental/NivenTan.lean`) the value is rational exactly when the reduced denominator of
`r` is `1, 2` (the value `0`) or `8` (`±1`) — returned exactly — the denominator `4` is a
**pole**, and every other value is irrational, which certifies the Ziv loop on `tanPeriodApprox`
(`AzFloat/TanWithPeriodBracket.lean`).  `tanPeriodCore` is this case distinction after the
reduction, shared with the rational variant.

**Poles** follow IEEE 754 (`tanPi (n + 1/2)` is `+∞` for even `n` and `−∞` for odd `n`): the
result at a pole is the infinity with the sign of `sin (2π x / u)`, i.e. `+∞` at
`x/u ≡ 1/4`, `−∞` at `x/u ≡ 3/4 (mod 1)`, exact (`.eq`).  (There is no negative zero: the zeros
of the tangent are returned as the unsigned `0`.)

Tiny arguments (`|2πx/u| < 2^(e+3)`, `2(e + 3) ≤ −(p + 72)`) are rounded by `tanPeriodTiny?`
before any reduction, at a cost independent of `e`.

Special values: `u = 0` gives `NaN`; `tan NaN = tan (±∞) = NaN`; `x = 0` gives `0`.
-/

namespace Azurite.AzFloat

/-- `± tan (2πr)` for a reduced rational `r ∈ [0, 1)` (`neg`: the sign is negative), rounded to
precision `p` with `mode`: `0` for the denominators `1, 2`, the signed infinity for `4` (the
poles: `+∞` at `r = 1/4`), `±1` for `8`, and otherwise the certified Ziv loop. -/
def tanPeriodCore (neg : Bool) (r : AzRat)
    (hr : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ) ∧ ((AzRat.toRat r : ℚ) : ℝ) < 1) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  if h1 : r.den = AzNat.ofNat 1 then (zero, .eq)
  else if h2 : r.den = AzNat.ofNat 2 then (zero, .eq)
  else if h4 : r.den = AzNat.ofNat 4 then
    (infinity (neg != decide (r.num = AzNat.ofNat 1)), .eq)
  else if h8 : r.den = AzNat.ofNat 8 then
    setPrecRound (signedPow2
      (neg != decide (r.num = AzNat.ofNat 1 ∨ r.num = AzNat.ofNat 5)) 0) p mode
  else
    zivLoopCertified (tanPeriodApprox neg r) p mode (p + zivGuardBits)
      (tanPeriodApprox_isSome_exists p mode neg r hr.1 hr.2 h1 h2 h4 h8 (p + zivGuardBits)
        (by unfold zivGuardBits; omega))

/-- `tan (2π x / u)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `u = 0`, and for `p = 0` unless `x = 0`); a signed infinity at the
poles. -/
def tanWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hu : u.toNat = 0 then (nan, .eq)
  else
    match x with
    | nan => (nan, .eq)
    | infinity _ => (nan, .eq)
    | zero => (zero, .eq)
    | finite s e _ m _ =>
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
          rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
        match tanPeriodTiny? (!s) m (AzNat.ofNat u.toNat) (e - (AzNat.ofNat m.size).toAzInt)
          (e + AzInt.ofInt 3) p mode with
        | some r => r
        | none =>
          tanPeriodCore (!s)
            (periodFrac m (e - (AzNat.ofNat m.size).toAzInt) (AzNat.ofNat u.toNat)) (by
              obtain ⟨_, _, hr0, hr1⟩ :=
                periodFrac_spec m (e - (AzNat.ofNat m.size).toAzInt) hun
              exact ⟨hr0, hr1⟩) p mode

/-- `tan (2π x / u)` rounded to nearest at the precision of `x`. -/
def tanWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (tanWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
