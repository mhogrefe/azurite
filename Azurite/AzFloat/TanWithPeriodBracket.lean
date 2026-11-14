/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosWithPeriodBracket
import Azurite.AzFloat.TanBracket

/-!
## The brackets of `tan (2π x / u)`

`tanPeriodBracket r w` encloses `tan (2πr)` for a rational `r ∈ [0, 1)` (the exact reduction
`periodFrac` of `|x|/u`) at Ziv level `w`: the quotient step `tanOfSinCos`
(`AzFloat/TanBracket.lean`) applied to the joint bracket `sinCosPeriodBracket r w` — or the
dummy bracket `[−1, 1]` while the bracket of `cos (2πr)` contains `0`.  `tanPeriodApprox neg`
negates and swaps the ends for a negative `x`.

**Tiny arguments** (`tanPeriodTinyBracket`, `tanPeriodTiny?`): for `x = ± m 2^E` with
`y = 2π m 2^E / u < 2^e'`, `e' ≤ 0`, the floats `ylo ≤ y ≤ yhi` of `sinPeriodTinyBracket` and
`y < tan y ≤ y + y·2^(2e')`.  One `roundingPossible` test at `p + 72` bits, at a cost independent
of `E`.
-/

namespace Azurite.AzFloat

/-- The bracket of `tan (2πr)` at Ziv level `w` for a rational `r ∈ [0, 1)`, or the dummy
bracket `[−1, 1]` when the bracket of `cos (2πr)` contains `0`. -/
def tanPeriodBracket (r : AzRat) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (sinCosPeriodBracket r w) (w + 12)

/-- The bracket of `± tan (2πr)` as a pair of `Roundable`s (negated and swapped for `neg`). -/
def tanPeriodApprox (neg : Bool) (r : AzRat) (w : Nat) : Roundable × Roundable :=
  negSwapApprox neg (tanPeriodBracket r w)

/-- The bracket of `tan y` for a tiny `y = 2π m 2^E / u < 2^e'` at precision `W`. -/
def tanPeriodTinyBracket (m u : AzNat) (E e' : AzInt) (W : Nat) : AzFloat × AzFloat :=
  let c := AzRat.ofAzNats m u
  let P := piBracket W
  let k := E + AzInt.ofInt 1
  let ylo := (mulPrecRound (ofAzRatRound c W .Floor).1 P.1 W .Floor).1 <<< k
  let yhi := (mulPrecRound (ofAzRatRound c W .Ceiling).1 P.2 W .Ceiling).1 <<< k
  (ylo, (addPrecRound yhi ((yhi <<< e') <<< e') W .Ceiling).1)

/-- **The tiny-argument path of `tan (2π x / u)`** for `|x| = m 2^E`, `|2πx/u| < 2^e'`
(`neg`: `x < 0`).  `none` when the argument is not tiny or the test fails. -/
def tanPeriodTiny? (neg : Bool) (m u : AzNat) (E e' : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if e'.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e'.abs.toNat then
    let b := tanPeriodTinyBracket m u E e' (p + zivGuardBits + 8)
    roundingPossible (negSwapApprox neg b).1 (negSwapApprox neg b).2 p mode
  else none

end Azurite.AzFloat
