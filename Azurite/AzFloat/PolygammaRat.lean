/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Polygamma
import Azurite.AzFloat.DigammaRat

/-!
## The polygamma functions of a rational

`polygammaRatPrecRound n q p mode` is `ψ⁽ⁿ⁾(q)` for an `AzRat` `q`, rounded to precision `p` in
`mode` with the comparison against the exact value; `polygammaRat n q p` rounds to nearest;
`trigammaRatPrecRound` and `trigammaRat` are the case `n = 1`.  The pieces are those of the
float function (`AzFloat/PolygammaBracket.lean`), the argument entering by the roundings of
rationals: of `q` itself for `q > 0`, and for `q < 0` of the exact rationals `q + m`,
`1 − q − m` (both in `(0, 1)`) and `1 − q`.

* **`n = 0`**: `digammaRatPrecRound`.
* **Special values, `n ≥ 1`**, as for a float: `(−1)ⁿ⁺¹ ∞` at `0`; at the negative integers
  `+∞` for an odd `n` and `NaN` for an even one.
* **Tiny arguments** (`polygammaRatTiny?`): the one test `polygammaTinyOf` on the roundings of
  `|q|`.
* **Fuel**, as for the float function: `polygammaRatPrecRound_eq_or`
  (`Equiv/PolygammaRat.lean`) is "correctly rounded, or `NaN`".
-/

namespace Azurite.AzFloat

/-- An enclosure of `H(q) = (−1)ⁿ⁺¹ ψ⁽ⁿ⁾(q)` at Ziv level `w` for a rational `q < 0` that is not
an integer, as `polygammaNegEncl`: with `m = −⌊q⌋`, so that `u = q + m` and `1 − u` lie in
`(0, 1)`, the recurrence in positive terms for `m ≤ 2^L`, and three positive arguments
beyond.  `u`, `1 − u` and `1 − q` are exact rationals, rounded once.  (`none` only if the
signs are not those of such a `q`.) -/
def polygammaRatNegEncl (n : Nat) (q : AzRat) (w : Nat) : Option Encl :=
  let k := (q.round .Floor).1
  let m := k.abs.toNat
  let u := q - k.toAzRat
  let a₂ := 1 - u
  if k.sign = false ∧ u.num ≠ 0 ∧ u.sign = true ∧ a₂.num ≠ 0 ∧ a₂.sign = true then
    let V := polyWork n w
    let W := w + 32
    let U := lnGammaRatEncl u V
    let A₂ := lnGammaRatEncl a₂ V
    if m ≤ 2 ^ lnGammaShiftExp w then
      let T := Encl.mul V (Encl.exact (ofAzNat (AzNat.factorial n))) (polyShiftSum V A₂ n m)
      some (if n % 2 = 1 then Encl.add W (polygammaPosEncl n U w) T
        else Encl.sub W (polygammaPosEncl n U w) T)
    else
      let A₁ := lnGammaRatEncl (1 - q) V
      let D := Encl.sub W (polygammaPosEncl n A₁ w) (polygammaPosEncl n A₂ w)
      some (if n % 2 = 0 then Encl.add W (polygammaPosEncl n U w) D
        else Encl.sub W (polygammaPosEncl n U w) D)
  else none

/-- An enclosure of `ψ⁽ⁿ⁾(q)` at Ziv level `w` for a rational `q` that is positive (`pos`) or
negative and not an integer. -/
def polygammaRatEncl (n : Nat) (q : AzRat) (pos : Bool) (w : Nat) : Option Encl :=
  (if pos then some (polygammaPosEncl n (lnGammaRatEncl q (polyWork n w)) w)
    else polygammaRatNegEncl n q w).map fun H => if n % 2 = 1 then H else Encl.neg H

/-- The bracket of `ψ⁽ⁿ⁾(q)` as a pair of `Roundable`s, with the second evaluation of
`enclRefine` where digits cancel. -/
def polygammaRatApprox (n : Nat) (q : AzRat) (pos : Bool) (p w : Nat) :
    Roundable × Roundable :=
  lnAbsGammaApproxOf (enclRefine (polygammaRatEncl n q pos) p w) w

/-- Is `q` tiny for `ψ⁽ⁿ⁾` at precision `p`: `|q| < 2^e` with
`(n + 1)(|e| − 2) ≥ p + 72 + lg (n + 1) + 2`, and `|q| ≤ 1/4` by its roundings at 64 bits (the
latter is what the proofs use). -/
def polygammaRatIsTiny (n : Nat) (q : AzRat) (e : AzInt) (p : Nat) : Bool :=
  !e.sign
    && decide (2 ≤ e.abs.toNat
      ∧ p + zivGuardBits + 10 + (n + 1).log2 ≤ (n + 1) * (e.abs.toNat - 2))
    && le (ofAzRatRound q 64 .Ceiling).1 (one <<< AzInt.ofInt (-2))
    && le (-(one <<< AzInt.ofInt (-2))) (ofAzRatRound q 64 .Floor).1

/-- **The tiny-argument path of `ψ⁽ⁿ⁾(q)`**, `n ≥ 1`, `q ≠ 0`: `polygammaTinyOf` on the
roundings of `|q|`. -/
def polygammaRatTiny? (n : Nat) (q : AzRat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if polygammaRatIsTiny n q e p then
    polygammaTinyOf n (lnGammaRatEncl (if q.sign then q else -q) (p + zivGuardBits + 8)) q.sign
      p mode
  else none

/-- `ψ⁽ⁿ⁾(q)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` where the function has no value, for `p = 0` unless the value is infinite, or
if the fuel runs out). -/
def polygammaRatPrecRound (n : Nat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if n = 0 then digammaRatPrecRound q p mode
  else if q.num = 0 then (infinity (n % 2 == 1), .eq)
  else if q.den = 1 ∧ q.sign = false then
    (if n % 2 = 1 then (infinity true, .eq) else (nan, .eq))
  else if p = 0 then (nan, .eq)
  else
    let e := gammaRatExp q
    match polygammaRatTiny? n q e p mode with
    | some r => r
    | none =>
      zivLoop (polygammaRatApprox n q q.sign p) p mode (lnGammaFuel p) (polygammaStart n e p)

/-- `ψ⁽ⁿ⁾(q)` rounded to nearest at precision `p`. -/
def polygammaRat (n : Nat) (q : AzRat) (p : Nat) : AzFloat :=
  (polygammaRatPrecRound n q p .Nearest).1

/-- The trigamma function `ψ′(q)` of a rational, rounded to precision `p` with `mode`. -/
def trigammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  polygammaRatPrecRound 1 q p mode

/-- `ψ′(q)` rounded to nearest at precision `p`. -/
def trigammaRat (q : AzRat) (p : Nat) : AzFloat := polygammaRat 1 q p

end Azurite.AzFloat
