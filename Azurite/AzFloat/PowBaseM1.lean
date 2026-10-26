/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PowBaseBracket

/-!
## `u^x − 1` for a natural base `u`

`powBaseM1PrecRound u x p mode` is `u^x − 1` for a 64-bit natural `u` and a float `x`,
correctly rounded to precision `p` in `mode`, with the comparison against the exact value;
`powBaseM1 u x` rounds to nearest at the precision of `x`.  A rational `u^x` (`powBaseExact?`,
`u^x = r^n`) gives the exact `r^n − 1` by one correctly rounded subtraction, or
`(1 − r^|n|) / r^|n|` by one division for `n < 0`; otherwise the certified Ziv loop (no fuel)
runs over `powBaseM1Approx` (the bracket of `x ln u` at the compensated precision, through
`expM1OfBracket`), total because `u^x − 1` is irrational.  Special values: `NaN` for `NaN` and
`1^(±∞)`; `0^x − 1 = −1` for `x > 0`, `+∞` for `x < 0`; `u^0 − 1 = 0`; `1^x − 1 = 0`;
`u^(+∞) − 1 = +∞`, `u^(−∞) − 1 = −1` for `u ≥ 2`, swapped for `u = 0`.  The specification
`powBaseM1PrecRound_eq_liftVal` is in `Equiv/PowBaseM1.lean`.
-/

namespace Azurite.AzFloat

/-- `−1` rounded to precision `p` (`(nan, .eq)` for `p = 0`). -/
def negOneRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq) else setPrecRound (-one) p mode

/-- `u^x − 1` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`). -/
def powBaseM1PrecRound (u : UInt64) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s =>
    if u.toNat = 0 then (if s then negOneRound p mode else (infinity true, .eq))
    else if u.toNat = 1 then (nan, .eq)
    else if s then (infinity true, .eq) else negOneRound p mode
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if h0 : u.toNat = 0 then (if s then negOneRound p mode else (infinity true, .eq))
    else if h1 : u.toNat = 1 then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match hx : powBaseExact? (finite s e q m hv) (AzNat.ofNat u.toNat) with
      | some (r, n) =>
        if n.sign then subPrecRound (ofAzNat (r.pow n.abs.toNat)) one p mode
        else
          divPrecRound (ofAzInt (1 - (r.pow n.abs.toNat).toAzInt)) (ofAzNat (r.pow n.abs.toNat))
            p mode
      | none =>
        zivLoopCertified (powBaseM1Approx (finite s e q m hv) e u) p mode
          (powBaseM1Start e u p)
          (powBaseM1Approx_isSome_exists p mode s e hv u (by omega)
            (AzNat.toNat_ofNat u.toNat ▸
              irrational_sub_one_of_powBaseExact?_none s e hv (AzNat.ofNat u.toNat)
                (by rw [AzNat.toNat_ofNat]; omega)
                (by rw [AzNat.toNat_ofNat]; exact u.toBitVec.isLt) hx)
            (powBaseM1Start e u p) (by unfold powBaseM1Start zivGuardBits; omega))

/-- `u^x − 1` rounded to nearest at the precision of `x`. -/
def powBaseM1 (u : UInt64) (x : AzFloat) : AzFloat :=
  (powBaseM1PrecRound u x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
