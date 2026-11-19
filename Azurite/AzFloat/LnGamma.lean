/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGammaBracket
import Azurite.AzFloat.Ziv
import Azurite.AzFloat.Compare
import Azurite.AzFloat.GammaBracket
import Azurite.AzFloat.LnEncl
import Azurite.AzFloat.RoundToInteger
import Azurite.AzFloat.Equiv.LnGammaCertificate

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
* **Fuel.**  The loop has fuel (`lnGammaFuel p`, the common `zivDefaultFuel`): a termination
  certificate would need `ln Γ(x)` to be irrational at the float `x`, which is known only in
  special cases.
  The specification `lnGammaPrecRound_eq_or` (`Equiv/LnGamma.lean`) is "correctly rounded, or
  `NaN`"; the fuel is not exhausted unless the value lies extremely close to a rounding
  boundary.
-/

namespace Azurite.AzFloat

/-- The bits lost near the zeros `x = 1` and `x = 2` of `ln Γ`: `k` when `x − 1` or `x − 2` is
about `2^(−k)` (`q` is the precision of `x`). -/
def lnGammaCancelBits (x : AzFloat) (q : Nat) : Nat :=
  let f := fun (d : AzFloat) => match d.exponent? with
    | some e => if e.sign then 0 else e.abs.toNat
    | none => 0
  max (f (subPrecRound x one (q + 2) .Nearest).1)
    (f (subPrecRound x (ofAzNat (AzNat.ofNat 2)) (q + 2) .Nearest).1)

/-- The fuel of the Ziv loops for `ln Γ`, `ψ` and the functions built on their brackets: the
common convention `zivDefaultFuel`. -/
def lnGammaFuel (p : Nat) : Nat := zivDefaultFuel p

/-- **`ln Γ(x)` with the fuel of its Ziv loop as an argument**: `ln Γ(x)` rounded to precision
`p` with `mode`, and the comparison with the exact value (`(nan, .eq)` for `p = 0` unless the
value is `0` or `+∞`, for `x < 0`, or if the fuel runs out).  At an integer `n ≥ 3` the value
`ln (n − 1)!` is irrational, and the loop is a certified one (`lnGammaApprox_cert_int`).  The
specification is `lnGammaPrecRoundFuel_zivSpec` (`Equiv/LnGamma.lean`). -/
def lnGammaPrecRoundFuel (fuel : Nat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (infinity true, .eq)
  | finite false _ _ _ _ => (nan, .eq)
  | finite true e q m hv =>
    if h12 : (eqIEEE (finite true e q m hv) one
        || eqIEEE (finite true e q m hv) (ofAzNat (AzNat.ofNat 2))) = true then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      if hI : isInteger (finite true e q m hv) = true then
        zivLoopCertified (lnGammaApprox (finite true e q m hv) e) p mode
          (max 64 (p + 32 + lnGammaCancelBits (finite true e q m hv) q))
          (lnGammaApprox_cert_int hv h12 hI p mode _ (by omega))
      else
        zivLoop (lnGammaApprox (finite true e q m hv) e) p mode fuel
          (max 64 (p + 32 + lnGammaCancelBits (finite true e q m hv) q))

/-- `ln Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`, for `x < 0`, or if the fuel runs
out): `lnGammaPrecRoundFuel` at the fuel `lnGammaFuel p`.  No fuel is involved at the
integers. -/
def lnGammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  lnGammaPrecRoundFuel (lnGammaFuel p) x p mode

/-- `ln Γ(x)` rounded to nearest at the precision of `x`. -/
def lnGamma (x : AzFloat) : AzFloat := (lnGammaPrecRound x (x.precision?.getD 1) .Nearest).1

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
  `lnAbsGammaPrecRound_eq_or` (`Equiv/LnGamma.lean`) is "correctly rounded, or `NaN`".
-/

section

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

/-- **`ln |Γ(x)|` with the fuel of its Ziv loop as an argument**: `ln |Γ(x)|` rounded to
precision `p` with `mode`, the comparison with the exact value, and the sign of `Γ(x)` (`true`:
positive).  The first component is `(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`, or
if the fuel runs out.  The specification is `lnAbsGammaPrecRoundFuel_zivSpec`. -/
def lnAbsGammaPrecRoundFuel (fuel : Nat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  match x with
  | nan => ((nan, .eq), true)
  | infinity _ => ((infinity true, .eq), true)
  | zero => ((infinity true, .eq), true)
  | finite true e q m hv => (lnGammaPrecRoundFuel fuel (finite true e q m hv) p mode, true)
  | finite false e q m hv =>
    if isInteger (finite false e q m hv) then ((infinity true, .eq), true)
    else
      (if p = 0 then (nan, .eq)
        else zivLoop (lnAbsGammaApprox (finite false e q m hv) e) p mode fuel
          (max 64 (p + 32)),
        gammaSign (finite false e q m hv))

/-- `ln |Γ(x)|` rounded to precision `p` with `mode`, the comparison with the exact value, and
the sign of `Γ(x)` (`true`: positive): `lnAbsGammaPrecRoundFuel` at the fuel `lnGammaFuel p`.
The first component is `(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`, or if the
fuel runs out. -/
def lnAbsGammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsGammaPrecRoundFuel (lnGammaFuel p) x p mode

/-- `ln |Γ(x)|` rounded to nearest at the precision of `x`, and the sign of `Γ(x)`. -/
def lnAbsGamma (x : AzFloat) : AzFloat × Bool :=
  let r := lnAbsGammaPrecRound x (x.precision?.getD 1) .Nearest
  (r.1.1, r.2)

end

end Azurite.AzFloat
