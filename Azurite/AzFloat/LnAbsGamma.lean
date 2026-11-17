/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.GammaBracket
import Azurite.AzFloat.LnEncl

/-!
## `ln |Γ(x)|` and the sign of `Γ(x)`

`lnAbsGammaPrecRound x p mode` is `ln |Γ(x)|` rounded to precision `p` in `mode`, with the
comparison against the exact value, together with the sign of `Γ(x)` (`true`: positive);
`lnAbsGamma x` rounds to nearest at the precision of `x`.  It extends `lnGammaPrecRound`
(`AzFloat/LnGamma.lean`) to the negative reals, with the special values of MPFR's
`mpfr_lgamma`:

* **Special values.**  `0` exactly at `x = 1` and `x = 2`; `+∞` at `±∞` and at the poles
  `x = 0, −1, −2, …`; `NaN` at `NaN`.
* **The sign.**  Positive for `x > 0`; for a negative `x` that is not an integer, that of
  `(−1)^⌈x⌉`, read off the parity of the truncation of `x`.  Where MPFR leaves it undefined
  (`NaN`, `−∞`, the negative integers) it is `true`, and so it is at `0` (there is no negative
  zero) and at `+∞`.
* **`x > 0`**: `lnGammaPrecRound`.
* **`x < 0`** (not an integer): the reflection formula (DLMF 5.5.3)
  `Γ(x) Γ(1 − x) = π / sin (π x)`, as
  `ln |Γ(x)| = ln (π / |sin (π x)|) − ln Γ(1 − x)`, with the sine of `gammaSinEncl`
  (`AzFloat/GammaBracket.lean`), which keeps its relative accuracy next to the poles and next
  to `0`, and the bracket of `ln Γ` at the enclosure of `1 − x`.  Between two poles below `−2`
  the value has two zeros, where the two terms cancel; Ziv's loop absorbs the bits lost there.
* **Fuel.**  The loop has fuel (`lnGammaFuel`): the specification
  `lnAbsGammaPrecRound_eq_or` (`Equiv/LnAbsGamma.lean`) is "correctly rounded, or `NaN`".
-/

namespace Azurite.AzFloat

/-- The reflection formula for `ln |Γ(x)|` on enclosures: from the answer `S` of the sine
(the sign and a positive enclosure of `|sin (π x)|`) and an enclosure `L` of `ln Γ(1 − x)`, the
enclosure of `ln (π / |sin (π x)|) − ln Γ(1 − x)`; `none` when the sine has none. -/
def lnAbsGammaReflect (S : Option (Bool × Encl)) (L : Encl) (w : Nat) : Option Encl :=
  match S with
  | none => none
  | some (_, S) =>
    some (Encl.sub (w + 16)
      (lnOfEncl (Encl.div (w + 16) (Encl.pi (w + 16)) S) (w + 16)) L)

/-- An enclosure of `ln |Γ(x)|` at Ziv level `w` for a finite `x < 0` of exponent `e` that is
not an integer; `none` when the sine has no positive enclosure at this level. -/
def lnAbsGammaNegEncl (x : AzFloat) (e : AzInt) (w : Nat) : Option Encl :=
  let e' := (if e.sign then e else 0) + 1
  let X₁ := Encl.add (w + 32) (Encl.exact (-x)) (Encl.exact one)
  lnAbsGammaReflect (gammaSinEncl x (w + 16) w) (lnGammaBracketEncl X₁ e' w) w

/-- An optional enclosure as a pair of `Roundable`s, the lower end strictly below the value;
the dummy bracket `[−1, 1]`, which is never accepted, when there is none. -/
def lnAbsGammaApproxOf (c : Option Encl) (w : Nat) : Roundable × Roundable :=
  match c with
  | none => negSwapApprox false (-one, one)
  | some b => lnGammaApproxOf b w

/-- The bracket of `ln |Γ(x)|`, `x < 0`, as a pair of `Roundable`s. -/
def lnAbsGammaApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  lnAbsGammaApproxOf (lnAbsGammaNegEncl x e w) w

/-- Is `Γ(x)` positive?  `true` for `x > 0`; for a negative `x` that is not an integer, whether
the truncation of `x` is odd; `true` in every other case. -/
def gammaSign (x : AzFloat) : Bool :=
  match x with
  | finite false e q m hv => (truncToAzInt (finite false e q m hv)).isOdd
  | _ => true

/-- `ln |Γ(x)|` rounded to precision `p` with `mode`, the comparison with the exact value, and
the sign of `Γ(x)` (`true`: positive).  The first component is `(nan, .eq)` for `p = 0` unless
the value is `0` or `+∞`, or if the fuel runs out. -/
def lnAbsGammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  match x with
  | nan => ((nan, .eq), true)
  | infinity _ => ((infinity true, .eq), true)
  | zero => ((infinity true, .eq), true)
  | finite true e q m hv => (lnGammaPrecRound (finite true e q m hv) p mode, true)
  | finite false e q m hv =>
    if isInteger (finite false e q m hv) then ((infinity true, .eq), true)
    else
      (if p = 0 then (nan, .eq)
        else zivLoop (lnAbsGammaApprox (finite false e q m hv) e) p mode lnGammaFuel
          (max 64 (p + 32)),
        gammaSign (finite false e q m hv))

/-- `ln |Γ(x)|` rounded to nearest at the precision of `x`, and the sign of `Γ(x)`. -/
def lnAbsGamma (x : AzFloat) : AzFloat × Bool :=
  let r := lnAbsGammaPrecRound x (x.precision?.getD 1) .Nearest
  (r.1.1, r.2)

end Azurite.AzFloat
