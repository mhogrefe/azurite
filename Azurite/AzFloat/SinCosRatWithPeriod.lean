/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosRatWithPeriod
import Azurite.AzFloat.SinRatWithPeriod
import Azurite.AzFloat.Equiv.SinCosWithPeriodBracket

/-!
## The sine and the cosine with a period of a rational together

`sinCosRatWithPeriodPrecRound q u p mode` is the pair of `sin (2π q / u)` and `cos (2π q / u)`
for an `AzRat` `q` and a `UInt64` period `u`, each correctly rounded to precision `p` in `mode`
with the comparison against the exact value:
`sinCosRatWithPeriodPrecRound q u p mode = (sinRatWithPeriodPrecRound q u p mode,
cosRatWithPeriodPrecRound q u p mode)` (`sinCosRatWithPeriodPrecRound_eq`,
`Equiv/SinCosRatWithPeriod.lean`), from **one** computation.  `sinCosRatWithPeriod q u p` rounds
both to nearest.

The rational counterpart of `sinCosWithPeriodPrecRound` on the same machinery: after the exact
reduction `r = periodFracRat q u ∈ [0, 1)`, when the reduced denominator of `r` is none of
`1, 2, 3, 4, 6, 12` both values are irrational and a certified joint Ziv loop
(`zivLoopCertified₂`) runs on `sinCosPeriodApprox`.  Everything else — `u = 0`, `q = 0`,
`p = 0`, tiny arguments and those six denominators — is delegated to
`sinRatWithPeriodPrecRound` and `cosRatWithPeriodPrecRound`.
-/

namespace Azurite.AzFloat

/-- `(sin (2π q / u), cos (2π q / u))` for a rational `q`, each rounded to precision `p` with
`mode` and paired with the comparison with the exact value, from one computation. -/
def sinCosRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × (AzFloat × Ordering) :=
  if hu : u.toNat = 0 then
    (sinRatWithPeriodPrecRound q u p mode, cosRatWithPeriodPrecRound q u p mode)
  else if h0 : q.num = 0 then
    (sinRatWithPeriodPrecRound q u p mode, cosRatWithPeriodPrecRound q u p mode)
  else if hp : p = 0 then
    (sinRatWithPeriodPrecRound q u p mode, cosRatWithPeriodPrecRound q u p mode)
  else
    haveI : NeZero p := ⟨hp⟩
    have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
      rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
    match sinPeriodTiny? (!q.sign) q.num (q.den * AzNat.ofNat u.toNat) (AzInt.ofInt 0)
      (ratExpBound q + AzInt.ofInt 2) p mode, cosTiny? (ratExpBound q + AzInt.ofInt 2) p mode with
    | none, none =>
      let r := periodFracRat q (AzNat.ofNat u.toNat)
      if h : r.den ≠ AzNat.ofNat 1 ∧ r.den ≠ AzNat.ofNat 2 ∧ r.den ≠ AzNat.ofNat 3 ∧
          r.den ≠ AzNat.ofNat 4 ∧ r.den ≠ AzNat.ofNat 6 ∧ r.den ≠ AzNat.ofNat 12 then
        zivLoopCertified₂ (sinCosPeriodApprox (!q.sign) r) p mode (p + zivGuardBits) (by
          obtain ⟨_, _, hr0, hr1⟩ := periodFracRat_spec q hun
          exact sinCosPeriodApprox_isSome_exists p mode (!q.sign) r hr0 hr1 h.1 h.2.1 h.2.2.1
            h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 (p + zivGuardBits)
            (by unfold zivGuardBits; omega))
      else (sinRatWithPeriodPrecRound q u p mode, cosRatWithPeriodPrecRound q u p mode)
    | _, _ => (sinRatWithPeriodPrecRound q u p mode, cosRatWithPeriodPrecRound q u p mode)

/-- `(sin (2π q / u), cos (2π q / u))`, both rounded to nearest at precision `p`. -/
def sinCosRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat × AzFloat :=
  let r := sinCosRatWithPeriodPrecRound q u p .Nearest
  (r.1.1, r.2.1)

end Azurite.AzFloat
