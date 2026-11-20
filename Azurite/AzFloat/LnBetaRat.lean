/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaRat
import Azurite.AzFloat.LnBeta
import Azurite.AzFloat.LnRat

/-!
## `ln B(a, b)`, and `ln |B(a, b)|` with the sign of `B(a, b)`, for two rationals

`lnAbsBetaRatPrecRound a b p mode` is `ln |B(a, b)|` for `AzRat`s `a`, `b`, rounded to precision
`p` in `mode` with the comparison against the exact value, together with the sign of `B(a, b)`
(`true`: positive); `lnAbsBetaRat a b p` rounds to nearest.  The loop is that of the float
function (`lnAbsLoop`, `AzFloat/LnBeta.lean`) on `lnAbsBetaEncl` at the enclosures of the
rationals, as in `AzFloat/BetaRat.lean`.

* **Special values**: `NaN` when `a` or `b` is a negative integer; `+∞` when one of them is
  `0`; `−∞` when `a + b` is a non-positive integer (`B = 0`).
* **Exact case**: `ln |B(a, 1)| = −ln |a|` by `lnRatPrecRound`.
* **Contract** (`Equiv/LnBetaRat.lean`): `lnAbsBetaRatPrecRound_eq_or`,
  `lnAbsBetaRatPrecRound_sign`.
-/

namespace Azurite.AzFloat

/-- `−ln |q|` rounded to precision `p` with `mode`. -/
def negLnAbsRat (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lnRatPrecRound q.abs p (-mode)
  (-r.1, r.2.swap)

/-- `ln |B(a, b)|` rounded to precision `p` with `mode`, the comparison with the exact value,
and the sign of `B(a, b)` (`true`: positive).  The first component is `(nan, .eq)` at a
negative integer, for `p = 0` unless the value is infinite, or if the fuel runs out.  The
fuel of the loop is explicit. -/
def lnAbsBetaRatPrecRoundFuel (fuel : Nat) (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  if betaRatPole a || betaRatPole b then ((nan, .eq), true)
  else if a.num = 0 ∨ b.num = 0 then ((infinity true, .eq), true)
  else if (a + b).den = 1 ∧ ((a + b).num = 0 ∨ (a + b).sign = false) then
    ((infinity false, .eq), true)
  else if p = 0 then ((nan, .eq), true)
  else if b.sign = true ∧ b.num = b.den then (negLnAbsRat a p mode, a.sign)
  else if a.sign = true ∧ a.num = a.den then (negLnAbsRat b p mode, b.sign)
  else
    let ea := gammaRatExp a
    let eb := gammaRatExp b
    let es := gammaRatExp (a + b)
    let bits := betaBits ea eb es
    lnAbsLoop (fun w => lnAbsBetaEncl (lnGammaRatEncl a) (lnGammaRatEncl b)
      (lnGammaRatEncl (a + b)) ea eb es (gammaRatFrac a) (gammaRatFrac b) (gammaRatFrac (a + b))
      (w + bits) w) p mode fuel (max 64 (p + 32))

/-- `ln |B(a, b)|` rounded to precision `p` with `mode`, the comparison with the exact value,
and the sign of `B(a, b)`: `lnAbsBetaRatPrecRoundFuel` at the fuel `gammaFuel p`.  The
specification of the value is `lnAbsBetaRatPrecRoundFuel_zivSpec` (`Equiv/LnBetaRat.lean`). -/
def lnAbsBetaRatPrecRound (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsBetaRatPrecRoundFuel (gammaFuel p) a b p mode

/-- `ln |B(a, b)|` rounded to nearest at precision `p`, and the sign of `B(a, b)`. -/
def lnAbsBetaRat (a b : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsBetaRatPrecRound a b p .Nearest
  (r.1.1, r.2)

/-- `ln B(a, b)` for two rationals, rounded to precision `p` with `mode`, and the comparison
with the exact value: `lnAbsBetaRatPrecRound` where `B(a, b) ≥ 0`, `(nan, .eq)` where
`B(a, b) < 0`. -/
def lnBetaRatPrecRoundFuel (fuel : Nat) (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  let r := lnAbsBetaRatPrecRoundFuel fuel a b p mode
  if r.2 then r.1 else (nan, .eq)

/-- `ln B(a, b)` for two rationals: `lnBetaRatPrecRoundFuel` at the fuel `gammaFuel p`
(`lnBetaRatPrecRoundFuel_zivSpec`, `Equiv/LnBetaRat.lean`). -/
def lnBetaRatPrecRound (a b : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  lnBetaRatPrecRoundFuel (gammaFuel p) a b p mode

/-- `ln B(a, b)` rounded to nearest at precision `p`. -/
def lnBetaRat (a b : AzRat) (p : Nat) : AzFloat := (lnBetaRatPrecRound a b p .Nearest).1

end Azurite.AzFloat
