/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CosPeriodBracket

/-!
## The cosine with a period of a rational: `cos (2π q / u)`

`cosRatWithPeriodPrecRound q u p mode` is `cos (2π q / u)` for an `AzRat` `q` and a `UInt64`
period `u`, correctly rounded to precision `p` in `mode`, with the comparison against the exact
value; `cosRatWithPeriod q u p` rounds to nearest.  The rational counterpart of
`cosWithPeriodPrecRound` (`AzFloat/CosPeriod.lean`), on the same machinery: the fractional part
`r = periodFracRat q u` of `|q| / u` is an exact reduced rational, `cos (2π q / u) = cos (2πr)`,
the reduced denominators `1, 2, 4, 3, 6` give the exact values `1, −1, 0, −1/2, 1/2` (Niven), and
otherwise the Ziv loop on `cosPeriodApprox r` is certified by the irrationality.  Tiny arguments
(`|2πq/u| < 2^(ratExpBound q + 2)`) are rounded by `cosTiny?` before the reduction.

Special values: `u = 0` or `p = 0` give `NaN`; `q = 0` gives `1`.
-/

namespace Azurite.AzFloat

/-- `cos (2π q / u)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `p = 0` or `u = 0`). -/
def cosRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hu : u.toNat = 0 then (nan, .eq)
  else if hp : p = 0 then (nan, .eq)
  else if h0 : q.num = 0 then setPrecRound one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
      rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
    match cosTiny? (ratExpBound q + AzInt.ofInt 2) p mode with
    | some r => r
    | none =>
    let r := periodFracRat q (AzNat.ofNat u.toNat)
    if h1 : r.den = AzNat.ofNat 1 then setPrecRound one p mode
    else if h2 : r.den = AzNat.ofNat 2 then setPrecRound (-one) p mode
    else if h4 : r.den = AzNat.ofNat 4 then (zero, .eq)
    else if h3 : r.den = AzNat.ofNat 3 then setPrecRound (-(one <<< AzInt.ofInt (-1))) p mode
    else if h6 : r.den = AzNat.ofNat 6 then setPrecRound (one <<< AzInt.ofInt (-1)) p mode
    else
      zivLoopCertified (cosPeriodApprox r) p mode (p + zivGuardBits) (by
        obtain ⟨_, _, hr0, hr1⟩ := periodFracRat_spec q hun
        exact cosPeriodApprox_isSome_exists p mode r hr0 hr1 h1 h2 h3 h4 h6
          (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `cos (2π q / u)` rounded to nearest at precision `p`. -/
def cosRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (cosRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
