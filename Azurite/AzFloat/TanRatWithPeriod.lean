/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanWithPeriod

/-!
## The tangent with a period of a rational: `tan (2π q / u)`

`tanRatWithPeriodPrecRound q u p mode` is `tan (2π q / u)` for an `AzRat` `q` and a `UInt64`
period `u`, correctly rounded to precision `p` in `mode`, with the comparison against the exact
value; `tanRatWithPeriod q u p` rounds to nearest.  The rational counterpart of
`tanWithPeriodPrecRound` (`AzFloat/TanWithPeriod.lean`), on the same machinery: the fractional
part `r = periodFracRat q u` of `|q| / u` is an exact reduced rational,
`tan (2π q / u) = ± tan (2πr)` with the sign of `q`, and `tanPeriodCore` returns `0` for the
reduced denominators `1, 2`, the signed infinity of IEEE 754 for `4` (the poles), `±1` for `8`,
and otherwise runs the certified Ziv loop.  Tiny arguments (`|2πq/u| < 2^e'`,
`e' = ratExpBound q + 2`, `p + 72 ≤ 2|e'|`) are rounded by `tanPeriodTiny?` before the reduction.

Special values: `u = 0` gives `NaN`; `q = 0` gives `0`; `p = 0` gives `NaN` unless `q = 0`.
-/

namespace Azurite.AzFloat

/-- `tan (2π q / u)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `u = 0`, and for `p = 0` unless `q = 0`); a signed infinity at the
poles. -/
def tanRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hu : u.toNat = 0 then (nan, .eq)
  else if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
      rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
    match tanPeriodTiny? (!q.sign) q.num (q.den * AzNat.ofNat u.toNat) (AzInt.ofInt 0)
      (ratExpBound q + AzInt.ofInt 2) p mode with
    | some r => r
    | none =>
      tanPeriodCore (!q.sign) (periodFracRat q (AzNat.ofNat u.toNat)) (by
        obtain ⟨_, _, hr0, hr1⟩ := periodFracRat_spec q hun
        exact ⟨hr0, hr1⟩) p mode

/-- `tan (2π q / u)` rounded to nearest at precision `p`. -/
def tanRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (tanRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
