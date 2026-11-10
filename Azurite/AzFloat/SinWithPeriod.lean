/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SinWithPeriodBracket

/-!
## The sine with a period: `sin (2π x / u)`

`sinWithPeriodPrecRound x u p mode` is `sin (2π x / u)` for a float `x` and a `UInt64` period
`u` (degrees for `u = 360`, turns for `u = 1`), correctly rounded to precision `p` in `mode`, with
the comparison against the exact value; `sinWithPeriod x u` rounds to nearest at the precision
of `x`.

The argument is reduced exactly: `|x|/u = m 2^E / u` has the fractional part
`r = periodFrac m E u ∈ [0, 1)` as a reduced rational, and
`sin (2π x / u) = ± sin (2πr)` with the sign of `x`.  By Niven's theorem for the sine
(`Transcendental/NivenSin.lean`) the value is rational exactly when the reduced denominator of
`r` is `1, 2` (the value `0`), `4` (`±1`) or `12` (`±1/2`) — returned exactly (rounded only to
`p` bits), the sign read off the numerator — and irrational otherwise, which certifies the Ziv
loop on `sinPeriodApprox` (`AzFloat/SinWithPeriodBracket.lean`).

Tiny arguments (`|2πx/u| < 2^(e+3)`, `2(e + 3) ≤ −(p + 72)`) are rounded by `sinPeriodTiny?`
before any reduction (the value is irrational: `0 < |x|/u < 1/12`), at a cost independent of
`e`.

Special values: `u = 0` gives `NaN`; `sin NaN = sin (±∞) = NaN`; `x = 0` gives `0`.
-/

namespace Azurite.AzFloat

/-- `sin (2π x / u)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `u = 0`, and for `p = 0` unless `x = 0`). -/
def sinWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
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
        match sinPeriodTiny? (!s) m (AzNat.ofNat u.toNat) (e - (AzNat.ofNat m.size).toAzInt)
          (e + AzInt.ofInt 3) p mode with
        | some r => r
        | none =>
        let r := periodFrac m (e - (AzNat.ofNat m.size).toAzInt) (AzNat.ofNat u.toNat)
        if h1 : r.den = AzNat.ofNat 1 then (zero, .eq)
        else if h2 : r.den = AzNat.ofNat 2 then (zero, .eq)
        else if h4 : r.den = AzNat.ofNat 4 then
          setPrecRound (signedPow2 (s == decide (r.num = AzNat.ofNat 1)) 0) p mode
        else if h12 : r.den = AzNat.ofNat 12 then
          setPrecRound (signedPow2
            (s == decide (r.num = AzNat.ofNat 1 ∨ r.num = AzNat.ofNat 5)) (-1)) p mode
        else
          zivLoopCertified (sinPeriodApprox (!s) r) p mode (p + zivGuardBits) (by
            obtain ⟨_, _, hr0, hr1⟩ :=
              periodFrac_spec m (e - (AzNat.ofNat m.size).toAzInt) hun
            exact sinPeriodApprox_isSome_exists p mode (!s) r hr0 hr1 h1 h2 h4 h12
              (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `sin (2π x / u)` rounded to nearest at the precision of `x`. -/
def sinWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (sinWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
