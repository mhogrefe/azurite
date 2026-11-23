/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BarnesGRat
import Azurite.AzFloat.LnBeta

/-!
## `ln G(x)`, and `ln |G(x)|` with the sign of `G(x)`, for the Barnes `G`-function

`lnAbsBarnesGPrecRound x p mode` is `ln |G(x)|` for a float `x`, rounded to precision `p` in
`mode` with the comparison against the exact value, together with the sign of `G(x)` (`true`:
positive or zero); `lnAbsBarnesG x` rounds to nearest at the precision of `x`.
`lnBarnesGPrecRound`, `lnBarnesG` are the logarithm of `G` itself: the same value where
`G(x) ≥ 0`, `NaN` where `G(x) < 0`.  The versions for an `AzRat`:
`lnAbsBarnesGRatPrecRound`, `lnAbsBarnesGRat`, `lnBarnesGRatPrecRound`, `lnBarnesGRat`.

The bracket of `G` is the exponential of an enclosure of `ln |G|` with the sign
(`barnesGLnEnclOf`, `AzFloat/BarnesGBracket.lean`); here that enclosure is rounded itself, by
the loop of `ln |B|` (`lnAbsLoop`, `AzFloat/LnBeta.lean`).

* **Special values**: `NaN ↦ NaN`; `ln G(+∞) = +∞`; `−∞ ↦ NaN`; **`−∞` at the zeros
  `0, −1, −2, …` of `G`**.
* **Exact case**: at a positive integer `n ≤ 64` the value is the logarithm of the integer
  `G(n) = ∏_{k ≤ n−2} k!` (`lnPrecRound`, no fuel): `0` at `n = 1, 2, 3`, irrational beyond.
* **Fuel** as for `G` (`barnesGFuel`, `barnesGRatFuel`).  Near `|G| = 1` the value is small
  against its terms and the loop supplies the bits; where `|G(x)| = 1` at a non-integer the
  value `0` is a rounding boundary and only the fuel ends the loop.

The specifications (`lnAbsBarnesGPrecRoundFuel_zivSpec`, …) are in `Equiv/LnBarnesG.lean`.
-/

namespace Azurite.AzFloat

/-- `ln |G|` with the sign on an argument of the bracket classified by `k`: `some none` at a
zero of `G`, `some (some n)` at a positive integer `n ≤ 64`, `none` otherwise. -/
def lnAbsBarnesGKind (A : BarnesIn) (k : Option (Option Nat)) (fuel p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  match k with
  | some none => ((infinity false, .eq), true)
  | some (some n) =>
    if p = 0 then ((nan, .eq), true) else (lnPrecRound (ofAzNat (barnesGNat n)) p mode, true)
  | none =>
    if p = 0 then ((nan, .eq), true)
    else lnAbsLoop (barnesGLnEnclOf A) p mode fuel (max 64 (p + 32))

/-- The class of a finite float. -/
def barnesKind (x : AzFloat) : Option (Option Nat) :=
  if isInteger x then
    if le x zero then some none
    else if le x (ofAzNat (AzNat.ofNat 64)) then some (some (truncToAzInt x).abs.toNat)
    else none
  else none

/-- The class of a rational. -/
def barnesRatKind (q : AzRat) : Option (Option Nat) :=
  if q.den = 1 then
    if q.num = 0 ∨ q.sign = false then some none
    else if le (ofAzNat q.num) (ofAzNat (AzNat.ofNat 64)) then some (some q.num.toNat)
    else none
  else none

/-- **`ln |G(x)|` rounded to precision `p` with `mode`, the comparison with the exact value,
and the sign of `G(x)`** (`true`: not negative), with the fuel of the loop explicit. -/
def lnAbsBarnesGPrecRoundFuel (fuel : Nat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  match x with
  | nan => ((nan, .eq), true)
  | infinity s => (if s then (infinity true, .eq) else (nan, .eq), true)
  | x => lnAbsBarnesGKind (barnesIn x) (barnesKind x) fuel p mode

/-- `ln |G(x)|` and the sign of `G(x)`: `lnAbsBarnesGPrecRoundFuel` at the fuel
`barnesGFuel x p`. -/
def lnAbsBarnesGPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsBarnesGPrecRoundFuel (barnesGFuel x p) x p mode

/-- `ln |G(x)|` rounded to nearest at the precision of `x`, and the sign of `G(x)`. -/
def lnAbsBarnesG (x : AzFloat) : AzFloat × Bool :=
  let r := lnAbsBarnesGPrecRound x (x.precision?.getD 1) .Nearest
  (r.1.1, r.2)

/-- `ln G(x)` with the fuel explicit: `ln |G(x)|` where `G(x) ≥ 0`, `(nan, .eq)` where
`G(x) < 0`. -/
def lnBarnesGPrecRoundFuel (fuel : Nat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  let r := lnAbsBarnesGPrecRoundFuel fuel x p mode
  if r.2 then r.1 else (nan, .eq)

/-- `ln G(x)` rounded to precision `p` with `mode`. -/
def lnBarnesGPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  lnBarnesGPrecRoundFuel (barnesGFuel x p) x p mode

/-- `ln G(x)` rounded to nearest at the precision of `x`. -/
def lnBarnesG (x : AzFloat) : AzFloat :=
  (lnBarnesGPrecRound x (x.precision?.getD 1) .Nearest).1

/-- **`ln |G(q)|` for a rational**, the comparison with the exact value, and the sign of
`G(q)`, with the fuel explicit. -/
def lnAbsBarnesGRatPrecRoundFuel (fuel : Nat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsBarnesGKind (barnesRatIn q) (barnesRatKind q) fuel p mode

/-- `ln |G(q)|` and the sign of `G(q)` at the fuel `barnesGRatFuel q p`. -/
def lnAbsBarnesGRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsBarnesGRatPrecRoundFuel (barnesGRatFuel q p) q p mode

/-- `ln |G(q)|` rounded to nearest at precision `p`, and the sign of `G(q)`. -/
def lnAbsBarnesGRat (q : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsBarnesGRatPrecRound q p .Nearest
  (r.1.1, r.2)

/-- `ln G(q)` for a rational with the fuel explicit (`(nan, .eq)` where `G(q) < 0`). -/
def lnBarnesGRatPrecRoundFuel (fuel : Nat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  let r := lnAbsBarnesGRatPrecRoundFuel fuel q p mode
  if r.2 then r.1 else (nan, .eq)

/-- `ln G(q)` rounded to precision `p` with `mode`. -/
def lnBarnesGRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  lnBarnesGRatPrecRoundFuel (barnesGRatFuel q p) q p mode

/-- `ln G(q)` rounded to nearest at precision `p`. -/
def lnBarnesGRat (q : AzRat) (p : Nat) : AzFloat := (lnBarnesGRatPrecRound q p .Nearest).1

end Azurite.AzFloat
