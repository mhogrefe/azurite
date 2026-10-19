/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LnBracket

/-!
## The natural logarithm

`ln x` by the AGM (MCA §4.8.2, `abs_pi_div_AGM_sub_log_le`): `x` is scaled by a power of two to
`y = x · 2^ℓ ∈ [2^(2h+1), 2^(2h+2))`, `ln y ≈ (π/2)/AGM(1, 4/y)` with error at most
`2^(−4h)(2h + 2)`, run on enclosures with directed rounding (`LnBracket.lean`), and
`ln x = ln y − ℓ ln 2` with the bracket of `ln 2`.  The result is rounded by the certified Ziv
loop: `ln x` is irrational for every rational `x ≠ 1` (`irrational_log_rat`) and the bracket
width tends to zero (`lnApprox_spec`), so `zivLoopCertified` needs no fuel and `lnPrecRound` is
total and proven correctly rounded (`Equiv/Ln.lean`).

The cost at precision `p` is dominated by the first Ziv level, `w = p + 64`: `2 ⌈lg (w/2 + 4)⌉ + 3`
AGM steps, each a multiplication, a square root and two additions at precision `w`, plus the
brackets of `π` and `ln 2` and three divisions.

Special values follow IEEE 754 / MPFR conventions: `ln NaN = NaN`, `ln (+∞) = +∞`, `ln 0 = −∞`,
`ln x = NaN` for `x < 0` (including `−∞`), and `ln 1 = 0` exactly.
-/

namespace Azurite.AzFloat

/-- `ln x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def lnPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (infinity false, .eq)
  | finite false _ _ _ _ => (nan, .eq)
  | finite true e q m hv =>
    if h1 : eqIEEE (finite true e q m hv) one = true then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (lnApprox (finite true e q m hv) e) p mode (p + zivGuardBits)
        (lnApprox_isSome_exists p mode e hv h1 (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `ln x` rounded to nearest at the precision of `x`. -/
def ln (x : AzFloat) : AzFloat := (lnPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
