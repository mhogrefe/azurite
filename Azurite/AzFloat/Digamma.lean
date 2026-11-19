/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.DigammaBracket
import Azurite.AzFloat.LnGamma

/-!
## The digamma function `ψ(x) = Γ′(x)/Γ(x)`

`digammaPrecRound x p mode` is `ψ(x)` (DLMF §5.2(i)) rounded to precision `p` in `mode`, with
the comparison against the exact value; `digamma x` rounds to nearest at the precision of `x`.

* **Special values.**  `ψ(+∞) = +∞`; `ψ(0) = −∞` (the limit from the right: there is no
  negative zero); `NaN` at the other poles `−1, −2, …`, at `−∞` and at `NaN`.
* **Rounding.**  A tiny argument goes through `digammaTiny?`; otherwise Ziv's loop on
  `digammaEncl` (`AzFloat/DigammaBracket.lean`): the shifted asymptotic series for `x > 0`,
  the reflection formula for `x < 0`.
* **Fuel.**  The loop has fuel (`lnGammaFuel p`, the common `zivDefaultFuel`): a termination
  certificate would need `ψ(x)` to be irrational at the float `x`, which is not known even
  for `ψ(1) = −γ`.
  The specification `digammaPrecRound_eq_or` (`Equiv/Digamma.lean`) is "correctly rounded, or
  `NaN`".  The zeros of `ψ` (`1.4616…` and one between any two consecutive poles) are not
  floats as far as anyone knows; next to one the loop doubles its precision until the value
  separates from `0`.
-/

namespace Azurite.AzFloat

/-- The bracket of `ψ(x)` as a pair of `Roundable`s, the lower end strictly below the value;
the dummy bracket `[−1, 1]` when there is no enclosure at this level. -/
def digammaApprox (x : AzFloat) (e : AzInt) (pos : Bool) (w : Nat) : Roundable × Roundable :=
  lnAbsGammaApproxOf (digammaEncl x e pos w) w

/-- The first working precision of the loop for an argument below `2^e`: `p + 32`, and `|e|`
more for a tiny argument whose one-test path failed. -/
def digammaStart (e : AzInt) (p : Nat) : Nat :=
  max 64 (p + 32
    + (if e.sign = false ∧ p + zivGuardBits + 8 ≤ e.abs.toNat then e.abs.toNat else 0))

/-- `ψ(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` at the negative integers, for `p = 0` unless the value is infinite, or if the
fuel runs out). -/
def digammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (infinity false, .eq)
  | finite s e q m hv =>
    if !s && isInteger (finite s e q m hv) then (nan, .eq)
    else if p = 0 then (nan, .eq)
    else
      match digammaTiny? (finite s e q m hv) e p mode with
      | some r => r
      | none =>
        zivLoop (digammaApprox (finite s e q m hv) e s) p mode (lnGammaFuel p) (digammaStart e p)

/-- `ψ(x)` rounded to nearest at the precision of `x`. -/
def digamma (x : AzFloat) : AzFloat := (digammaPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
