/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CosWithPeriodBracket

/-!
## The cosine with a period: `cos (2π x / u)`

`cosWithPeriodPrecRound x u p mode` is `cos (2π x / u)` for a float `x` and a `UInt64` period
`u` (degrees for `u = 360`, turns for `u = 1`), correctly rounded to precision `p` in `mode`, with
the comparison against the exact value; `cosWithPeriod x u` rounds to nearest at the precision
of `x`.

The argument is reduced exactly: `x/u = m 2^E / u` has the fractional part
`r = periodFrac m E u ∈ [0, 1)` as a reduced rational, and `cos (2π x / u) = cos (2πr)`.  By
Niven's theorem (`Transcendental/Niven.lean`) the value is rational exactly when the reduced
denominator of `r` is `1, 2, 3, 4` or `6` — the values `1, −1, −1/2, 0, 1/2`, returned exactly
(rounded only to `p` bits) — and irrational otherwise, which certifies the Ziv loop on
`cosPeriodApprox r` (`AzFloat/CosWithPeriodBracket.lean`).

Tiny arguments (`|2πx/u| < 2^(e+3)`, `e + 3 ≤ −(p + 72)`) are rounded by `cosTiny?` before any
reduction (the value is irrational: `0 < |x|/u < 1/6`), at a cost independent of `e`.

Special values: `u = 0` gives `NaN`; `cos NaN = cos (±∞) = NaN`; `x = 0` gives `1`.
-/

namespace Azurite.AzFloat

/-- `cos (2π x / u)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `p = 0` or `u = 0`). -/
def cosWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
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
        match cosTiny? (e + AzInt.ofInt 3) p mode with
        | some r => r
        | none =>
        let r := periodFrac m (e - (AzNat.ofNat m.size).toAzInt) (AzNat.ofNat u.toNat)
        if h1 : r.den = AzNat.ofNat 1 then setPrecRound one p mode
        else if h2 : r.den = AzNat.ofNat 2 then setPrecRound (-one) p mode
        else if h4 : r.den = AzNat.ofNat 4 then (zero, .eq)
        else if h3 : r.den = AzNat.ofNat 3 then setPrecRound (-(one <<< AzInt.ofInt (-1))) p mode
        else if h6 : r.den = AzNat.ofNat 6 then setPrecRound (one <<< AzInt.ofInt (-1)) p mode
        else
          zivLoopCertified (cosPeriodApprox r) p mode (p + zivGuardBits) (by
            obtain ⟨_, _, hr0, hr1⟩ :=
              periodFrac_spec m (e - (AzNat.ofNat m.size).toAzInt) hun
            exact cosPeriodApprox_isSome_exists p mode r hr0 hr1 h1 h2 h3 h4 h6
              (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `cos (2π x / u)` rounded to nearest at the precision of `x`. -/
def cosWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (cosWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
