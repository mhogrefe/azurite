/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Polygamma
import Azurite.AzFloat.Equiv.PolygammaRatCertificate
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

/-- **`ψ⁽ⁿ⁾(q)` rounded to precision `p` with `mode`, with the fuel of the Ziv loop explicit**
(`(nan, .eq)` where the function has no value, for `p = 0` unless the value is infinite, or
if the fuel runs out; for `n = 0` it is `digammaRatPrecRound`).  For an odd `n` at a positive
integer or a rational of denominator `2` the value is irrational and the loop is backed by a
certified one (`polygammaRatApprox_cert`).  The specification is
`polygammaRatPrecRoundFuel_zivSpec` (`Equiv/PolygammaRat.lean`). -/
def polygammaRatPrecRoundFuel (fuel : Nat) (n : Nat) (q : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if n = 0 then digammaRatPrecRoundFuel fuel q p mode
  else if h0 : q.num = 0 then (infinity (n % 2 == 1), .eq)
  else if hpole : q.den = 1 ∧ q.sign = false then
    (if n % 2 = 1 then (infinity true, .eq) else (nan, .eq))
  else if hp : p = 0 then (nan, .eq)
  else
    match polygammaRatTiny? n q (gammaRatExp q) p mode with
    | some r => r
    | none =>
      if hc : polygammaRatSpecial n q = true then
        haveI : NeZero p := ⟨hp⟩
        zivLoopBacked (polygammaRatApprox n q q.sign p) p mode fuel
          (polygammaStart n (gammaRatExp q) p)
          (polygammaRatApprox_cert h0 hpole hc p mode _
            (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _)))
      else
        zivLoop (polygammaRatApprox n q q.sign p) p mode fuel
          (polygammaStart n (gammaRatExp q) p)

/-- `ψ⁽ⁿ⁾(q)` rounded to precision `p` with `mode`, and the comparison with the exact value:
`polygammaRatPrecRoundFuel` at the fuel `lnGammaFuel p`. -/
def polygammaRatPrecRound (n : Nat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  polygammaRatPrecRoundFuel (lnGammaFuel p) n q p mode

/-- `ψ⁽ⁿ⁾(q)` rounded to nearest at precision `p`. -/
def polygammaRat (n : Nat) (q : AzRat) (p : Nat) : AzFloat :=
  (polygammaRatPrecRound n q p .Nearest).1

/-- The trigamma function `ψ′(q)` of a rational, rounded to precision `p` with `mode`. -/
def trigammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  polygammaRatPrecRound 1 q p mode

/-- `ψ′(q)` rounded to nearest at precision `p`. -/
def trigammaRat (q : AzRat) (p : Nat) : AzFloat := polygammaRat 1 q p

end Azurite.AzFloat
