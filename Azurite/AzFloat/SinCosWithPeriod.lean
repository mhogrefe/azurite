/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosWithPeriod
import Azurite.AzFloat.SinWithPeriod
import Azurite.AzFloat.Equiv.SinCosWithPeriodBracket

/-!
## The sine and the cosine with a period together: `sin (2π x / u)`, `cos (2π x / u)`

`sinCosWithPeriodPrecRound x u p mode` is the pair of `sin (2π x / u)` and `cos (2π x / u)` for
a float `x` and a `UInt64` period `u`, each correctly rounded to precision `p` in `mode` with
the comparison against the exact value:
`sinCosWithPeriodPrecRound x u p mode = (sinWithPeriodPrecRound x u p mode,
cosWithPeriodPrecRound x u p mode)` (`sinCosWithPeriodPrecRound_eq`,
`Equiv/SinCosWithPeriod.lean`), from **one** computation.  `sinCosWithPeriod x u` rounds both to
nearest at the precision of `x`.

After the exact reduction `r = periodFrac m E u ∈ [0, 1)`, when the reduced denominator of `r`
is none of `1, 2, 3, 4, 6, 12` both values are irrational (Niven's theorem), and a certified
joint Ziv loop (`zivLoopCertified₂`, no fuel) runs on `sinCosPeriodApprox`
(`AzFloat/SinCosWithPeriodBracket.lean`).  Everything else — `u = 0`, `NaN`, `±∞`, zero,
`p = 0`, tiny arguments (where `sinPeriodTiny?` or `cosTiny?` answers) and the denominators
`1, 2, 3, 4, 6, 12` (where at least one value is rational, hence exact) — is delegated to
`sinWithPeriodPrecRound` and `cosWithPeriodPrecRound`.
-/

namespace Azurite.AzFloat

/-- `(sin (2π x / u), cos (2π x / u))`, each rounded to precision `p` with `mode` and paired
with the comparison with the exact value (as `sinWithPeriodPrecRound` and
`cosWithPeriodPrecRound`), from one computation. -/
def sinCosWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × (AzFloat × Ordering) :=
  if hu : u.toNat = 0 then
    (sinWithPeriodPrecRound x u p mode, cosWithPeriodPrecRound x u p mode)
  else
    match x with
    | finite s e q m hv =>
      if hp : p = 0 then
        (sinWithPeriodPrecRound (finite s e q m hv) u p mode,
          cosWithPeriodPrecRound (finite s e q m hv) u p mode)
      else
        haveI : NeZero p := ⟨hp⟩
        have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
          rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
        match sinPeriodTiny? (!s) m (AzNat.ofNat u.toNat) (e - (AzNat.ofNat m.size).toAzInt)
          (e + AzInt.ofInt 3) p mode, cosTiny? (e + AzInt.ofInt 3) p mode with
        | none, none =>
          let r := periodFrac m (e - (AzNat.ofNat m.size).toAzInt) (AzNat.ofNat u.toNat)
          if h : r.den ≠ AzNat.ofNat 1 ∧ r.den ≠ AzNat.ofNat 2 ∧ r.den ≠ AzNat.ofNat 3 ∧
              r.den ≠ AzNat.ofNat 4 ∧ r.den ≠ AzNat.ofNat 6 ∧ r.den ≠ AzNat.ofNat 12 then
            zivLoopCertified₂ (sinCosPeriodApprox (!s) r) p mode (p + zivGuardBits) (by
              obtain ⟨_, _, hr0, hr1⟩ :=
                periodFrac_spec m (e - (AzNat.ofNat m.size).toAzInt) hun
              exact sinCosPeriodApprox_isSome_exists p mode (!s) r hr0 hr1 h.1 h.2.1 h.2.2.1
                h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 (p + zivGuardBits)
                (by unfold zivGuardBits; omega))
          else
            (sinWithPeriodPrecRound (finite s e q m hv) u p mode,
              cosWithPeriodPrecRound (finite s e q m hv) u p mode)
        | _, _ =>
          (sinWithPeriodPrecRound (finite s e q m hv) u p mode,
            cosWithPeriodPrecRound (finite s e q m hv) u p mode)
    | _ => (sinWithPeriodPrecRound x u p mode, cosWithPeriodPrecRound x u p mode)

/-- `(sin (2π x / u), cos (2π x / u))`, both rounded to nearest at the precision of `x`. -/
def sinCosWithPeriod (x : AzFloat) (u : UInt64) : AzFloat × AzFloat :=
  let r := sinCosWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest
  (r.1.1, r.2.1)

end Azurite.AzFloat
