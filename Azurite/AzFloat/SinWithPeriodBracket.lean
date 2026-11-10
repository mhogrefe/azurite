/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinBracket
import Azurite.AzFloat.CosWithPeriodBracket

/-!
## The brackets of `sin (2π x / u)`

`sinPeriodBracket r w` encloses `sin (2πr)` for a rational `r ∈ [0, 1)` (the exact reduction
`periodFrac` of `|x|/u`) at Ziv level `w`: with `W = cosWork 3 w`, the float
`t = ⌊2 ⌊r⌋_W · lo⌋_W` (`lo` the lower end of `piBracket W`) satisfies `0 ≤ 2πr − t ≤ 48·2^(−W)`,
so `sinBracket t 3 w` widened by `2^(6−W)` encloses `sin (2πr)` (Lipschitz).  `sinPeriodApprox`
negates and swaps the ends for a negative `x`.

**Tiny arguments** (`sinPeriodTinyBracket`, `sinPeriodTiny?`): for `x = ± m 2^E` with
`y = 2π m 2^E / u < 2^e'`, `e' ≤ 0`, the rational `c = m/u` and the bracket of `π` give floats
`ylo ≤ y ≤ yhi` (the exponent `E` enters only through exact shifts, so the cost is independent
of it), and `y − y·2^(2e') < sin y < y`.  One `roundingPossible` test at `p + 72` bits.
-/

namespace Azurite.AzFloat

/-- The bracket of `sin (2πr)` at Ziv level `w` for a rational `r ∈ [0, 1)`. -/
def sinPeriodBracket (r : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let W := cosWork (AzInt.ofInt 3) w
  let P := piBracket W
  let a := (ofAzRatRound r W .Floor).1
  let t := (mulPrecRound (a <<< AzInt.ofInt 1) P.1 W .Floor).1
  let E := one <<< AzInt.ofInt (6 - W)
  Encl.widen W (sinBracket t (AzInt.ofInt 3) w) (Encl.exact E)

/-- The bracket of `± sin (2πr)` as a pair of `Roundable`s (negated and swapped for `neg`). -/
def sinPeriodApprox (neg : Bool) (r : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := sinPeriodBracket r w
  if neg then (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)
  else (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `sin y` for a tiny `y = 2π m 2^E / u < 2^e'` at precision `W`. -/
def sinPeriodTinyBracket (m u : AzNat) (E e' : AzInt) (W : Nat) : AzFloat × AzFloat :=
  let c := AzRat.ofAzNats m u
  let P := piBracket W
  let k := E + AzInt.ofInt 1
  let ylo := (mulPrecRound (ofAzRatRound c W .Floor).1 P.1 W .Floor).1 <<< k
  let yhi := (mulPrecRound (ofAzRatRound c W .Ceiling).1 P.2 W .Ceiling).1 <<< k
  ((subPrecRound ylo ((yhi <<< e') <<< e') W .Floor).1, yhi)

/-- **The tiny-argument path of `sin (2π x / u)`** for `|x| = m 2^E`, `|2πx/u| < 2^e'`
(`neg`: `x < 0`).  `none` when the argument is not tiny or the test fails. -/
def sinPeriodTiny? (neg : Bool) (m u : AzNat) (E e' : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if e'.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e'.abs.toNat then
    let b := sinPeriodTinyBracket m u E e' (p + zivGuardBits + 8)
    if neg then
      roundingPossible (fun P M => setPrecRound (-b.2) P M) (fun P M => setPrecRound (-b.1) P M)
        p mode
    else
      roundingPossible (fun P M => setPrecRound b.1 P M) (fun P M => setPrecRound b.2 P M) p mode
  else none

/-- `± 2^k` as a float. -/
def signedPow2 (pos : Bool) (k : Int) : AzFloat :=
  if pos then one <<< AzInt.ofInt k else -(one <<< AzInt.ofInt k)

end Azurite.AzFloat
