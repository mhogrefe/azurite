/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Beta
import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Ln

/-!
## `ln B(a, b)`, and `ln |B(a, b)|` with the sign of `B(a, b)`

`lnAbsBetaPrecRound a b p mode` is `ln |B(a, b)|` rounded to precision `p` in `mode`, with the
comparison against the exact value, together with the sign of `B(a, b)` (`true`: positive);
`lnAbsBeta a b` rounds to nearest at the larger of the two precisions.  It is to `betaPrecRound`
(`AzFloat/Beta.lean`) what `lnAbsGammaPrecRound` is to `Γ`: the value stays representable where
`B` itself overflows or underflows any practical exponent.

* **Special values** are those of `B`, through the logarithm: `NaN` where `B` is (`NaN`, `−∞`,
  a negative integer argument, `B(+∞, b)` for `b ≤ 0`); `+∞` where `B = +∞` (an argument `0`);
  **`−∞` where `B = 0`** (`B(+∞, b)` for `b > 0`, and `a + b` a non-positive integer).
* **Exact case**: `ln |B(a, 1)| = −ln |a|` is a logarithm (and `0` exactly at `a = 1`).
* **Rounding.**  `lnAbsLoop`: Ziv's loop with fuel on `lnAbsBetaCore`
  (`AzFloat/BetaBracket.lean`), which gives an enclosure of `ln |B|` and the sign of `B` at
  once — the bracket of `B` is its exponential.  The sign returned is the one of the level
  that produced the rounding.  Near `|B| = 1` the value is small against its terms and the
  loop supplies the bits.
* **Contract** (`Equiv/LnBeta.lean`): `lnAbsBetaPrecRound_eq_or` — correctly rounded, or
  `(nan, .eq)` when the fuel runs out — and `lnAbsBetaPrecRound_sign`: whenever the value is
  not `NaN`, the sign component is the sign of `B(a, b)`.  Where the value is `NaN` or
  infinite the sign component is `true`.

`lnBetaPrecRound a b p mode` and `lnBeta a b` are the logarithm of `B` itself: the same value
where `B(a, b) > 0`, `NaN` where `B(a, b) < 0` (`lnBetaPrecRound_eq_or`).
-/

namespace Azurite.AzFloat

/-- One level of the loop: from the answer `(neg, L)` of the core — `L` an enclosure of the
logarithm of the absolute value, `neg` the sign — the rounding, if it is determined, with the
sign (`true`: positive). -/
def lnAbsStep (core : Nat → Option (Bool × Encl)) (p : Nat) (mode : RoundingMode) (w : Nat) :
    Option ((AzFloat × Ordering) × Bool) :=
  match core w with
  | none => none
  | some (neg, L) =>
    (roundingPossible (lnGammaApproxOf L w).1 (lnGammaApproxOf L w).2 p mode).map
      fun r => (r, !neg)

/-- Ziv's loop with fuel for a logarithm of an absolute value with a sign: the working
precision is doubled until a level answers; `((nan, .eq), true)` when the fuel runs out. -/
def lnAbsLoop (core : Nat → Option (Bool × Encl)) (p : Nat) (mode : RoundingMode) :
    Nat → Nat → (AzFloat × Ordering) × Bool
  | 0, w => (lnAbsStep core p mode w).getD ((nan, .eq), true)
  | fuel + 1, w =>
    match lnAbsStep core p mode w with
    | some r => r
    | none => lnAbsLoop core p mode fuel (2 * w)

/-- `−ln |x|` rounded to precision `p` with `mode`. -/
def negLnAbs (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lnPrecRound x.abs p (-mode)
  (-r.1, r.2.swap)

/-- `ln |B(a, b)|` and the sign of `B(a, b)` for finite `a`, `b` (zero included). -/
def lnAbsBetaReal (a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  if isNegInt a || isNegInt b then ((nan, .eq), true)
  else if isZeroVal a || isZeroVal b then ((infinity true, .eq), true)
  else if sumIsNonposInt a b then ((infinity false, .eq), true)
  else if p = 0 then ((nan, .eq), true)
  else if isOneVal b then (negLnAbs a p mode, lt zero a)
  else if isOneVal a then (negLnAbs b p mode, lt zero b)
  else
    let ea := expOf a
    let eb := expOf b
    let bits := betaBits ea eb ((if ea ≤ eb then eb else ea) + 1)
    lnAbsLoop (fun w => lnAbsBetaCore a b (w + bits) w) p mode (gammaFuel p) (max 64 (p + 32))

/-- `ln |B(+∞, y)|`: `−∞` for `y > 0` (where `B = 0`), `NaN` otherwise. -/
def lnAbsBetaInfinite (y : AzFloat) : AzFloat × Ordering :=
  if lt zero y then (infinity false, .eq) else (nan, .eq)

/-- `ln |B(a, b)|` rounded to precision `p` with `mode`, the comparison with the exact value,
and the sign of `B(a, b)` (`true`: positive).  The first component is `(nan, .eq)` where `B` is
`NaN`, for `p = 0` unless the value is infinite, or if the fuel runs out. -/
def lnAbsBetaPrecRound (a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  match a, b with
  | nan, _ => ((nan, .eq), true)
  | _, nan => ((nan, .eq), true)
  | infinity s, b => (if s then lnAbsBetaInfinite b else (nan, .eq), true)
  | a, infinity s => (if s then lnAbsBetaInfinite a else (nan, .eq), true)
  | a, b => lnAbsBetaReal a b p mode

/-- `ln |B(a, b)|` rounded to nearest at the larger of the precisions of `a` and `b`, and the
sign of `B(a, b)`. -/
def lnAbsBeta (a b : AzFloat) : AzFloat × Bool :=
  let r := lnAbsBetaPrecRound a b (max (a.precision?.getD 1) (b.precision?.getD 1)) .Nearest
  (r.1.1, r.2)

/-- `ln B(a, b)` rounded to precision `p` with `mode`, and the comparison with the exact
value: `lnAbsBetaPrecRound` where `B(a, b) ≥ 0`, `(nan, .eq)` where `B(a, b) < 0` (and where
`B` is `NaN`, for `p = 0` unless the value is infinite, or if the fuel runs out). -/
def lnBetaPrecRound (a b : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lnAbsBetaPrecRound a b p mode
  if r.2 then r.1 else (nan, .eq)

/-- `ln B(a, b)` rounded to nearest at the larger of the precisions of `a` and `b`. -/
def lnBeta (a b : AzFloat) : AzFloat :=
  (lnBetaPrecRound a b (max (a.precision?.getD 1) (b.precision?.getD 1)) .Nearest).1

end Azurite.AzFloat
