/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PowBaseBracket

/-!
## `u^q` for a natural base `u` and a rational `q`

`powBaseRatPrecRound u q p mode` is `u^q` for a 64-bit natural `u` and a rational `q`, correctly
rounded to precision `p` in `mode`, with the comparison against the exact value;
`powBaseRat u q p` rounds to nearest.  A rational `u^q` (`powBaseRatExact?`: `s q` an integer
for `u = r^s` with `r` the primitive root of `u`; this includes `q = 0` and every integer `q`)
is the exact `r^n`, rounded once (a division for `n < 0`); otherwise the certified Ziv loop (no
fuel) runs over `powBaseRatApprox`, total because every other `u^q` is irrational.  Special
values: `0^q = 0` for `q > 0`, `+∞` for `q < 0`, `0^0 = 1`; `1^q = 1`.  The specification
`powBaseRatPrecRound_eq` is in `Equiv/PowBaseRat.lean`.
-/

namespace Azurite.AzFloat

/-- `u^q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`). -/
def powBaseRatPrecRound (u : UInt64) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : u.toNat = 0 then
    if q.num = 0 then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
    else if q.sign then (zero, .eq) else (infinity true, .eq)
  else if hp : p = 0 then (nan, .eq)
  else if h1 : u.toNat = 1 then setPrecRound one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    match hx : powBaseRatExact? q (AzNat.ofNat u.toNat) with
    | some (r, n) =>
      if n.sign then setPrecRound (ofAzNat (r.pow n.abs.toNat)) p mode
      else divPrecRound one (ofAzNat (r.pow n.abs.toNat)) p mode
    | none =>
      zivLoopCertified (powBaseRatApprox q u) p mode (powBaseRatStart q u p)
        (powBaseRatApprox_isSome_exists p mode q u (by omega)
          (AzNat.toNat_ofNat u.toNat ▸
            irrational_of_powBaseRatExact?_none q (AzNat.ofNat u.toNat)
              (by rw [AzNat.toNat_ofNat]; omega)
              (by rw [AzNat.toNat_ofNat]; exact u.toBitVec.isLt) hx)
          (powBaseRatStart q u p) (by unfold powBaseRatStart zivGuardBits; omega))

/-- `u^q` rounded to nearest at precision `p`. -/
def powBaseRat (u : UInt64) (q : AzRat) (p : Nat) : AzFloat :=
  (powBaseRatPrecRound u q p .Nearest).1

end Azurite.AzFloat
