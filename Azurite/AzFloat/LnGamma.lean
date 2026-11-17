/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGammaBracket
import Azurite.AzFloat.Ziv
import Azurite.AzFloat.Compare

/-!
## The logarithm of the gamma function, `ln Γ(x)` for `x > 0`

`lnGammaPrecRound x p mode` is `ln Γ(x)` (DLMF §5.2, §5.11) rounded to precision `p` in `mode`,
with the comparison against the exact value; `lnGamma x` rounds to nearest at the precision of
`x`.

* **Special values.**  `ln Γ(1) = ln Γ(2) = 0` exactly; `ln Γ(+∞) = +∞`; `ln Γ(0) = +∞` (the
  limit from the right); `NaN` for `x < 0`, `−∞` and `NaN`.  (Negative arguments, where `Γ`
  changes sign between the poles, are left for the reflection formula.)
* **Rounding.**  Ziv's loop on `lnGammaBracket` (`AzFloat/LnGammaBracket.lean`: an argument shift
  and Stirling's series with its proven remainder).  Near the zeros `x = 1` and `x = 2` the
  value is about `|x − 1|` or `|x − 2|` while the terms of the formula are of order `1`, so the
  first working precision is `p + 32` plus the bits lost there (`lnGammaCancelBits`).
* **Fuel.**  The loop has fuel (`lnGammaFuel`, ten doublings): a termination certificate would
  need `ln Γ(x)` to be irrational at the float `x`, which is known only in special cases.
  The specification `lnGammaPrecRound_eq_or` (`Equiv/LnGamma.lean`) is "correctly rounded, or
  `NaN`"; the fuel is not exhausted unless the value lies within about `2^(−1000 p)` of a
  rounding boundary.
-/

namespace Azurite.AzFloat

/-- The bracket of `ln Γ(x)` as a pair of `Roundable`s, the lower end lowered by one unit in
its last place so that it is strictly below the value. -/
def lnGammaApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := lnGammaBracket x e w
  let lo := (subPrecRound b.1 (powerOf2 (-(AzNat.ofNat (4 * w)).toAzInt)) (2 * w + 64) .Floor).1
  (fun p mode => setPrecRound lo p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bits lost near the zeros `x = 1` and `x = 2` of `ln Γ`: `k` when `x − 1` or `x − 2` is
about `2^(−k)` (`q` is the precision of `x`). -/
def lnGammaCancelBits (x : AzFloat) (q : Nat) : Nat :=
  let f := fun (d : AzFloat) => match d.exponent? with
    | some e => if e.sign then 0 else e.abs.toNat
    | none => 0
  max (f (subPrecRound x one (q + 2) .Nearest).1)
    (f (subPrecRound x (ofAzNat (AzNat.ofNat 2)) (q + 2) .Nearest).1)

/-- The fuel of the Ziv loop for `ln Γ`: ten doublings of the working precision. -/
def lnGammaFuel : Nat := 10

/-- `ln Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`, for `x < 0`, or if the fuel runs
out). -/
def lnGammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (infinity true, .eq)
  | finite false _ _ _ _ => (nan, .eq)
  | finite true e q m hv =>
    if eqIEEE (finite true e q m hv) one
        || eqIEEE (finite true e q m hv) (ofAzNat (AzNat.ofNat 2)) then (zero, .eq)
    else if p = 0 then (nan, .eq)
    else
      zivLoop (lnGammaApprox (finite true e q m hv) e) p mode lnGammaFuel
        (max 64 (p + 32 + lnGammaCancelBits (finite true e q m hv) q))

/-- `ln Γ(x)` rounded to nearest at the precision of `x`. -/
def lnGamma (x : AzFloat) : AzFloat := (lnGammaPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
