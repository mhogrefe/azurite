/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BarnesGBracket
import Azurite.AzFloat.Conversion

/-!
## The Barnes `G`-function

`barnesGPrecRound x p mode` is `G(x)` (DLMF §5.17; `G(z + 1) = Γ(z) G(z)`, `G(1) = 1`,
`G(n) = (n − 2)! ⋯ 1!`) for a float `x`, rounded to precision `p` in `mode` with the
comparison against the exact value; `barnesG x` rounds to nearest at the precision of `x`.

* **Special values.**  `NaN ↦ NaN`, `G(+∞) = +∞`, `G(−∞) = NaN` (`G` oscillates).  **`G` is
  `0` exactly at `0, −1, −2, …`.**
* **Exact values**: at a positive integer `n ≤ max 64 ⌊√(4p + 64)⌋` the integer
  `G(n) = ∏_{k ≤ n−2} k!` is formed (`barnesGNat`) and rounded.  (Beyond that bound `G(n)` has
  far more than `p` significant bits.)
* **Rounding.**  Ziv's loop with fuel (`barnesGFuel`: that of `Γ`, and `64` more doublings for a
  negative argument) on the bracket of
  `AzFloat/BarnesGBracket.lean`; `barnesGPrecRoundFuel` has the fuel as an argument.  The
  specification is `barnesGPrecRoundFuel_zivSpec` (`Equiv/BarnesG.lean`): correctly rounded or
  `NaN` at every fuel, correctly rounded for every large enough fuel wherever the value is no
  rounding boundary (the bracket converges: `Equiv/BarnesGWidth.lean`), and correct at every
  fuel on the special values, the zeros and the integers up to `64`.  Nothing is known about
  the arithmetic nature of the other values, so the fuel stays.
* **Cost.**  For a negative `x` the shift, and the cost, grow with `|x|`: there is no
  reflection formula in elementary functions.  The fuel of a negative argument is practically
  unbounded: an astronomically negative argument runs (or exhausts the memory) rather than
  giving a `NaN` for want of fuel.
-/

namespace Azurite.AzFloat

/-- After `s` more steps from `(k, f, g) = (k, k!, ∏_{i ≤ k} i!)`: `∏_{i ≤ k + s} i!`. -/
def barnesGNatAux : Nat → Nat → AzNat → AzNat → AzNat
  | 0, _, _, g => g
  | s + 1, k, f, g => barnesGNatAux s (k + 1) (f.mulNat (k + 1)) (g * f.mulNat (k + 1))

/-- `G(n) = ∏_{k=1}^{n−2} k!` for a positive integer `n` (the superfactorial of `n − 2`). -/
def barnesGNat (n : Nat) : AzNat := barnesGNatAux (n - 2) 0 1 1

/-- The positive integers up to this bound are evaluated exactly at precision `p`. -/
def barnesGExactBound (p : Nat) : Nat := max 64 (4 * p + 64).sqrt

/-- `G(x)` for a finite `x` (zero included), with the fuel of the Ziv loop explicit. -/
def barnesGRealFuel (fuel : Nat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if isInteger x then
    if le x zero then (zero, .eq)
    else if p = 0 then (nan, .eq)
    else if le x (ofAzNat (AzNat.ofNat (barnesGExactBound p))) then
      setPrecRound (ofAzNat (barnesGNat (truncToAzInt x).abs.toNat)) p mode
    else zivLoop (barnesGApprox x) p mode fuel (max 64 (p + 32))
  else if p = 0 then (nan, .eq)
  else zivLoop (barnesGApprox x) p mode fuel (max 64 (p + 32))

/-- **`G(x)` rounded to precision `p` with `mode`, with the fuel of the Ziv loop explicit**,
and the comparison with the exact value.  The specification is
`barnesGPrecRoundFuel_zivSpec` (`Equiv/BarnesG.lean`). -/
def barnesGPrecRoundFuel (fuel : Nat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | x => barnesGRealFuel fuel x p mode

/-- The fuel of `G`: that of `Γ`, and for a negative argument `64` more doublings of the
working precision — practically unbounded, so that a negative argument is never answered with
a `NaN` for want of fuel. -/
def barnesGFuel (x : AzFloat) (p : Nat) : Nat :=
  if lt x zero then gammaFuel p + 64 else gammaFuel p

/-- `G(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`, or if the fuel runs out):
`barnesGPrecRoundFuel` at the fuel `barnesGFuel x p`. -/
def barnesGPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  barnesGPrecRoundFuel (barnesGFuel x p) x p mode

/-- `G(x)` rounded to nearest at the precision of `x`. -/
def barnesG (x : AzFloat) : AzFloat :=
  (barnesGPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
