/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PowBaseBracket
import Azurite.AzFloat.PowBaseM1

/-!
## `u^q − 1` for a natural base `u` and a rational `q`

`powBaseM1RatPrecRound u q p mode` is `u^q − 1` for a 64-bit natural `u` and a rational `q`,
correctly rounded to precision `p` in `mode`, with the comparison against the exact value;
`powBaseM1Rat u q p` rounds to nearest.  `q = 0` gives `0` exactly; a rational `u^q = r^n`
(`powBaseRatExact?`) gives the exact `r^n − 1` by one correctly rounded subtraction, or
`(1 − r^|n|) / r^|n|` by one division for `n < 0`; otherwise the certified Ziv loop (no fuel)
runs over `powBaseM1RatApprox`, total because `u^q − 1` is irrational.  Special values:
`0^q − 1 = −1` for `q > 0`, `+∞` for `q < 0`, `0^0 − 1 = 0`; `1^q − 1 = 0`.  The specification
`powBaseM1RatPrecRound_eq` is in `Equiv/PowBaseM1Rat.lean`.
-/

namespace Azurite.AzFloat

/-- `u^q − 1` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`). -/
def powBaseM1RatPrecRound (u : UInt64) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : u.toNat = 0 then
    if q.num = 0 then (zero, .eq) else if q.sign then negOneRound p mode else (infinity true, .eq)
  else if h1 : u.toNat = 1 then (zero, .eq)
  else if hq0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match hx : powBaseRatExact? q (AzNat.ofNat u.toNat) with
    | some (r, n) =>
      if n.sign then subPrecRound (ofAzNat (r.pow n.abs.toNat)) one p mode
      else
        divPrecRound (ofAzInt (1 - (r.pow n.abs.toNat).toAzInt)) (ofAzNat (r.pow n.abs.toNat))
          p mode
    | none =>
      zivLoopCertified (powBaseM1RatApprox q u) p mode (powBaseM1RatStart q u p)
        (powBaseM1RatApprox_isSome_exists p mode q hq0 u (by omega)
          (AzNat.toNat_ofNat u.toNat ▸
            irrational_sub_one_of_powBaseRatExact?_none q (AzNat.ofNat u.toNat)
              (by rw [AzNat.toNat_ofNat]; omega)
              (by rw [AzNat.toNat_ofNat]; exact u.toBitVec.isLt) hx)
          (powBaseM1RatStart q u p) (by unfold powBaseM1RatStart zivGuardBits; omega))

/-- `u^q − 1` rounded to nearest at precision `p`. -/
def powBaseM1Rat (u : UInt64) (q : AzRat) (p : Nat) : AzFloat :=
  (powBaseM1RatPrecRound u q p .Nearest).1

end Azurite.AzFloat
