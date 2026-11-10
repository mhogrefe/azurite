/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SinWithPeriodBracket

/-!
## The sine with a period of a rational: `sin (2π q / u)`

`sinRatWithPeriodPrecRound q u p mode` is `sin (2π q / u)` for an `AzRat` `q` and a `UInt64`
period `u`, correctly rounded to precision `p` in `mode`, with the comparison against the exact
value; `sinRatWithPeriod q u p` rounds to nearest.  The rational counterpart of
`sinWithPeriodPrecRound` (`AzFloat/SinWithPeriod.lean`), on the same machinery: the fractional
part `r = periodFracRat q u` of `|q| / u` is an exact reduced rational,
`sin (2π q / u) = ± sin (2πr)` with the sign of `q`, the reduced denominators `1, 2`, `4`, `12`
give the exact values `0`, `±1`, `±1/2` (Niven for the sine), and otherwise the Ziv loop on
`sinPeriodApprox` is certified by the irrationality.  Tiny arguments
(`|2πq/u| < 2^e'`, `e' = ratExpBound q + 2`, `p + 72 ≤ 2|e'|`) are rounded by `sinPeriodTiny?`
(with `m = num q`, the denominator `den q · u` and no shift) before the reduction.

Special values: `u = 0` gives `NaN`; `q = 0` gives `0`; `p = 0` gives `NaN` unless `q = 0`.
-/

namespace Azurite.AzFloat

/-- `sin (2π q / u)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `u = 0`, and for `p = 0` unless `q = 0`). -/
def sinRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hu : u.toNat = 0 then (nan, .eq)
  else if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
      rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
    match sinPeriodTiny? (!q.sign) q.num (q.den * AzNat.ofNat u.toNat) (AzInt.ofInt 0)
      (ratExpBound q + AzInt.ofInt 2) p mode with
    | some r => r
    | none =>
    let r := periodFracRat q (AzNat.ofNat u.toNat)
    if h1 : r.den = AzNat.ofNat 1 then (zero, .eq)
    else if h2 : r.den = AzNat.ofNat 2 then (zero, .eq)
    else if h4 : r.den = AzNat.ofNat 4 then
      setPrecRound (signedPow2 (q.sign == decide (r.num = AzNat.ofNat 1)) 0) p mode
    else if h12 : r.den = AzNat.ofNat 12 then
      setPrecRound (signedPow2
        (q.sign == decide (r.num = AzNat.ofNat 1 ∨ r.num = AzNat.ofNat 5)) (-1)) p mode
    else
      zivLoopCertified (sinPeriodApprox (!q.sign) r) p mode (p + zivGuardBits) (by
        obtain ⟨_, _, hr0, hr1⟩ := periodFracRat_spec q hun
        exact sinPeriodApprox_isSome_exists p mode (!q.sign) r hr0 hr1 h1 h2 h4 h12
          (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `sin (2π q / u)` rounded to nearest at precision `p`. -/
def sinRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (sinRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
