/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PowBaseBracket

/-!
## `u^x` for a natural base `u`

`powBasePrecRound u x p mode` is `u^x` for a 64-bit natural `u` and a float `x`, correctly
rounded to precision `p` in `mode`, with the comparison against the exact value; `powBase u x`
rounds to nearest at the precision of `x`.  A rational `u^x` (`powBaseExact?`: `x s` an integer
for `u = r^s` with `r` the primitive root of `u`) is the exact `r^n`, rounded once (a division
for `n < 0`); otherwise the certified Ziv loop (no fuel) runs over `powBaseApprox`, total
because every other `u^x` is irrational.  Special values: `NaN` for `NaN` and for `1^(±∞)`;
`0^x = 0` for `x > 0`, `+∞` for `x < 0`; `u^0 = 1` (including `0^0`); `1^x = 1`;
`u^(+∞) = +∞` and `u^(−∞) = 0` for `u ≥ 2`, swapped for `u = 0`.  The specification
`powBasePrecRound_eq_liftVal` is in `Equiv/PowBase.lean`.
-/

namespace Azurite.AzFloat

/-- `u^x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is a special one). -/
def powBasePrecRound (u : UInt64) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s =>
    if u.toNat = 0 then (if s then (zero, .eq) else (infinity true, .eq))
    else if u.toNat = 1 then (nan, .eq)
    else if s then (infinity true, .eq) else (zero, .eq)
  | zero => if p = 0 then (nan, .eq) else setPrecRound one p mode
  | finite s e q m hv =>
    if h0 : u.toNat = 0 then (if s then (zero, .eq) else (infinity true, .eq))
    else if hp : p = 0 then (nan, .eq)
    else if h1 : u.toNat = 1 then setPrecRound one p mode
    else
      haveI : NeZero p := ⟨hp⟩
      match hx : powBaseExact? (finite s e q m hv) (AzNat.ofNat u.toNat) with
      | some (r, n) =>
        if n.sign then setPrecRound (ofAzNat (r.pow n.abs.toNat)) p mode
        else divPrecRound one (ofAzNat (r.pow n.abs.toNat)) p mode
      | none =>
        zivLoopCertified (powBaseApprox (finite s e q m hv) e u) p mode (powBaseStart e u p)
          (powBaseApprox_isSome_exists p mode s e hv u (by omega)
            (AzNat.toNat_ofNat u.toNat ▸
              irrational_of_powBaseExact?_none s e hv (AzNat.ofNat u.toNat)
                (by rw [AzNat.toNat_ofNat]; omega)
                (by rw [AzNat.toNat_ofNat]; exact u.toBitVec.isLt) hx)
            (powBaseStart e u p) (by unfold powBaseStart zivGuardBits; omega))

/-- `u^x` rounded to nearest at the precision of `x`. -/
def powBase (u : UInt64) (x : AzFloat) : AzFloat :=
  (powBasePrecRound u x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
