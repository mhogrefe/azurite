/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Digamma
import Azurite.AzFloat.GammaRat

/-!
## The digamma function of a rational

`digammaRatPrecRound q p mode` is `ψ(q)` for an `AzRat` `q`, rounded to precision `p` in `mode`
with the comparison against the exact value; `digammaRat q p` rounds to nearest.  The pieces
are those of the float function (`AzFloat/DigammaBracket.lean`), the argument entering by
enclosures of rationals: the roundings of `q` (or of `1 − q`, an exact rational, for `q < 0`)
for the asymptotic series, and those of `|q − k|`, `k` the integer nearest to `q`, for the
cotangent of the reflection formula.

* **Special values.**  `ψ(0) = −∞`; `NaN` at the negative integers.
* **Tiny arguments** (`digammaRatTiny?`): `−ψ(q)` lies in `(1/q, 1/q + 2)`, rounded from the
  outward roundings of the two rational ends.
* **Fuel**, as for the float function: `digammaRatPrecRound_eq_or` (`Equiv/DigammaRat.lean`) is
  "correctly rounded, or `NaN`".
-/

namespace Azurite.AzFloat

/-- The sign of `q − k` (`true`: negative) and a positive enclosure of `|q − k|`, `k` the
integer nearest to `q`; `none` when `q` is an integer. -/
def digammaRatFrac (q : AzRat) (W : Nat) : Option (Bool × Encl) :=
  let k := (q.round .Nearest).1
  let d := q - k.toAzRat
  if d.num = 0 then none
  else some (!d.sign, lnGammaRatEncl (if d.sign then d else -d) W)

/-- An enclosure of `ψ(q)` at Ziv level `w` for a rational `q ≠ 0` that is positive (`pos`) or
negative and not an integer, with `|q| < 2^e`. -/
def digammaRatEncl (q : AzRat) (e : AzInt) (pos : Bool) (w : Nat) : Option Encl :=
  if pos then some (digammaPosEncl (lnGammaRatEncl q (w + 32)) e w)
  else
    let e' := (if e.sign then e else 0) + 1
    digammaReflect (digammaRatFrac q (w + 16))
      (digammaPosEncl (lnGammaRatEncl (1 - q) (w + 32)) e' w) w

/-- The bracket of `ψ(q)` as a pair of `Roundable`s. -/
def digammaRatApprox (q : AzRat) (e : AzInt) (pos : Bool) (w : Nat) : Roundable × Roundable :=
  lnAbsGammaApproxOf (digammaRatEncl q e pos w) w

/-- Is `q` tiny at precision `p`: `|q| < 2^e` with `e ≤ −(p + 72)`, and `|q| ≤ 1/4` by its
roundings at 64 bits (the latter is what the proofs use). -/
def digammaRatIsTiny (q : AzRat) (e : AzInt) (p : Nat) : Bool :=
  !e.sign && decide (p + zivGuardBits + 8 ≤ e.abs.toNat)
    && le (ofAzRatRound q 64 .Ceiling).1 (one <<< AzInt.ofInt (-2))
    && le (-(one <<< AzInt.ofInt (-2))) (ofAzRatRound q 64 .Floor).1

/-- **The tiny-argument path of `ψ(q)`**: `−ψ(q)` lies in `(1/q, 1/q + 2)`, rounded in the
negated mode from the outward roundings of the two rational ends. -/
def digammaRatTiny? (q : AzRat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if digammaRatIsTiny q e p then
    let W := p + zivGuardBits + 8
    let r := q⁻¹
    let lo := (ofAzRatRound r W .Floor).1
    let hi := (ofAzRatRound (r + 1 + 1) W .Ceiling).1
    (roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p
      (-mode)).map fun r => (-r.1, r.2.swap)
  else none

/-- The first working precision of the loop: `p + 32`, and `|e|` more for a tiny argument
whose one-test path failed. -/
def digammaRatStart (q : AzRat) (e : AzInt) (p : Nat) : Nat :=
  max 64 (p + 32 + (if digammaRatIsTiny q e p then e.abs.toNat else 0))

/-- `ψ(q)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` at the negative integers, for `p = 0` unless the value is `−∞`, or if the fuel
runs out). -/
def digammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then (infinity false, .eq)
  else if q.den = 1 ∧ q.sign = false then (nan, .eq)
  else if p = 0 then (nan, .eq)
  else
    let e := gammaRatExp q
    match digammaRatTiny? q e p mode with
    | some r => r
    | none => zivLoop (digammaRatApprox q e q.sign) p mode lnGammaFuel (digammaRatStart q e p)

/-- `ψ(q)` rounded to nearest at precision `p`. -/
def digammaRat (q : AzRat) (p : Nat) : AzFloat := (digammaRatPrecRound q p .Nearest).1

end Azurite.AzFloat
