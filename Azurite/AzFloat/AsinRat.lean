/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AsinRatBracket
import Azurite.AzFloat.Atan2
import Azurite.AzFloat.PiConstants

/-!
## The arcsine of a rational

`asinRatPrecRound q p mode` is `arcsin q` for an `AzRat` `q`, correctly rounded to precision `p`
in `mode`, with the comparison against the exact value; `asinRat q p` rounds to nearest.

Special values, as for the float `asinPrecRound`: `arcsin 0 = 0` exactly; `arcsin (±1) = ±π/2`
(correctly rounded); `NaN` for `|q| > 1`.  Tiny arguments (`|q| < 2^e`, `e ≤ −(p + 72)`) by
`asinTinyRat?`; otherwise a certified Ziv loop (`zivLoopCertified`, no fuel) on `asinRatApprox`
(`AzFloat/AsinRatBracket.lean`), total because `arcsin q` is irrational for every rational
`q ≠ 0` in `[−1, 1]`.  The argument is never rounded to the target precision: `1 − q²` is formed
exactly as a rational, so `arcsin (1/3)` is the arcsine of one third and a rational next to
`±1` keeps its distance to `±1`.

The specification `asinRatPrecRound_eq` is in `Equiv/AsinRat.lean`.
-/

namespace Azurite.AzFloat

/-- `arcsin q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|q| > 1`, and for `p = 0` unless `q = 0`). -/
def asinRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if h1 : q.num = q.den then signedRound q.sign piDiv2PrecRound p mode
  else if hle : q.num ≤ q.den then
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match asinTinyRat? q p mode with
      | some r => r
      | none =>
        zivLoopCertified (asinRatApprox q) p mode (p + zivGuardBits)
          (asinRatApprox_isSome_exists p mode q h0
            (lt_of_le_of_ne ((abs_toRat_le_one_iff q).mp hle)
              (fun h => h1 ((abs_toRat_eq_one_iff q).mp h)))
            (p + zivGuardBits) (by unfold zivGuardBits; omega))
  else (nan, .eq)

/-- `arcsin q` rounded to nearest at precision `p`. -/
def asinRat (q : AzRat) (p : Nat) : AzFloat := (asinRatPrecRound q p .Nearest).1

end Azurite.AzFloat
