/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pochhammer

/-!
## The generalized Pochhammer symbol `(x)_y = Γ(x + y) / Γ(x)`

`genPochhammerPrecRound x y p mode` is `Γ(x + y)/Γ(x)` for floats `x`, `y`, rounded to
precision `p` in `mode`, with the comparison against the exact value; `genPochhammer x y`
rounds to nearest at the larger of the precisions of `x` and `y`.

* **An integer `y ≥ 0`**: Pochhammer's symbol `(x)ₙ`, `n = y` (`pochReal`) — a polynomial in
  `x`, also where `Γ(x)` has a pole (the limit of the quotient).
* **An integer `y < 0`**, `n = −y`: `1 / ((x − 1)(x − 2) ⋯ (x − n))`, again the limit at the
  poles of `Γ(x)`; a pole of its own, `NaN`, at `x = 1, …, n` (`genPochPole`).  An exact
  quotient of integers where that is cheap (`recipPochExact?`), otherwise the reciprocal of
  the enclosure of the product (`recipPochCore`, on `pochCoreOf`).
* **Otherwise** (`y` not an integer): `0` at the poles `x = 0, −1, −2, …` of `Γ(x)`; `NaN` at
  the poles `x + y = 0, −1, −2, …` of `Γ(x + y)`; elsewhere Ziv's loop with fuel on
  `genPochCore`: the exponential of

    `ln |Γ(x + y)| − ln |Γ(x)| = t_s − t_x + ½ ln (q_s / q_x)`

  from two pieces of `ln |Γ|` (`lnGammaPiece`, `AzFloat/BetaBracket.lean`: Stirling's series,
  with the reflection formula for a negative argument), sharing the table of tangent
  numbers, `π` and one logarithm.
* **Infinite arguments**: `NaN`.
* **Contract** (`Equiv/GenPochhammer.lean`): `genPochhammerPrecRound_eq_or` — correctly
  rounded, or `(nan, .eq)` when the fuel runs out.

The cost grows with the size of `ln Γ` at the arguments: for a large `x` and a small `y` the
two logarithms cancel, and the working precision pays for it.
-/

namespace Azurite.AzFloat

/-! ### A negative integer `y = −n`: `1 / ((x − n)ₙ)` -/

/-- Does a factor of `(x − 1) ⋯ (x − n)` vanish: is `x` an integer with `1 ≤ x ≤ n`? -/
def genPochPole (x : AzFloat) (n : Nat) : Bool :=
  isInteger x && lt zero x && le x (ofAzNat (AzNat.ofNat n))

/-- `1 / ∏_{j<n} (N/D − n + j) = Dⁿ / ∏_{j<n} (N − n D + j D)` as one correctly rounded
division of two exact floats. -/
def recipPochIntQuot (N D : AzInt) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  divPrecRound (ofAzInt (D.pow n)) (ofAzInt (risingInt (N - (n : AzInt) * D) D n)) p mode

/-- **The exact path** of the reciprocal, under the conditions of `pochExact?`. -/
def recipPochExact? (x : AzFloat) (n p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if (decide (n ≤ 128) && betaIntModerate x p) || pochExactCheap (pochFloatBits x) n p then
    x.toAzRat?.map fun q =>
      recipPochIntQuot (AzInt.mkNorm q.sign q.num) q.den.toAzInt n p mode
  else none

/-- The number of negative factors among `x − n, …, x − 1`, off the poles. -/
def recipPochSplit (x : AzFloat) (n : Nat) : Nat :=
  if le (ofAzNat (AzNat.ofNat n)) x then 0
  else if le x zero then n
  else n - (truncToAzInt x).abs.toNat

/-- The sign of `1 / (s)ₙ` and a positive enclosure of its absolute value, for an `s` given by
its enclosures `S V` and a split at `k ≤ n` negative factors: the reciprocal of
`pochCoreOf`. -/
def recipPochCoreOf (S : Nat → Encl) (k n bits w : Nat) : Option (Bool × Encl) :=
  (pochCoreOf S k n bits w).map fun r => (r.1, Encl.div (w + 32) (Encl.exact one) r.2)

/-- The sign of `1 / ((x − n)ₙ)` and a positive enclosure of its absolute value. -/
def recipPochCore (x : AzFloat) (n w : Nat) : Option (Bool × Encl) :=
  recipPochCoreOf (fun V => Encl.sub V (Encl.exact x) (Encl.nat n)) (recipPochSplit x n) n
    (gammaLnBits (expOf (addPrecRound x.abs (ofAzNat (AzNat.ofNat n)) 64 .Ceiling).1)) w

/-- `Γ(x − n)/Γ(x) = 1 / ((x − 1) ⋯ (x − n))` for a finite `x`. -/
def genPochNegInt (x : AzFloat) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if genPochPole x n then (nan, .eq)
  else if p = 0 then (nan, .eq)
  else
    match recipPochExact? x n p mode with
    | some r => r
    | none =>
      zivLoop (fun w => gammaApproxOf (recipPochCore x n w) w) p mode gammaFuel
        (max 64 (p + 32))

/-! ### A `y` that is not an integer -/

/-- `(neg, b)`: the sign of `Γ(s)/Γ(x)` and an enclosure `b` of `ln |Γ(s)/Γ(x)|` at level `w`
(with the sines at level `ws`), for arguments given by enclosures: `X V`, `S V` enclose `x`,
`s` (below `2^ex`, `2^es`) at the working precision `V`, and `Fx W`, `Fs W` give their
distances to an integer.  `none` when a piece is missing. -/
def lnAbsGammaQuotEncl (X S : Nat → Encl) (ex es : AzInt)
    (Fx Fs : Nat → Option (Bool × AzInt × Encl)) (w ws : Nat) : Option (Bool × Encl) :=
  let L := lnGammaShiftExp w
  let V := w + 2 * L + 8 + 2 * w.log2
  let pe := fun (e : AzInt) => max (L + 1) (if e.sign then e.abs.toNat else 0)
  let M := max (lnGammaTerms w (pe ex)) (lnGammaTerms w (pe es))
  let T := AzNat.tangentNumbers M
  let tol := powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)
  let Pi := Encl.pi V
  match lnGammaPiece (S V) es (fun _ => Fs (ws + 16)) Pi L V M T tol ws,
    lnGammaPiece (X V) ex (fun _ => Fx (ws + 16)) Pi L V M T tol ws with
  | some (ns, ts, qs), some (nx, tx, qx) =>
    some (ns != nx, Encl.add V (Encl.sub V ts tx) (Encl.half (lnOfEncl (Encl.div V qs qx) V)))
  | _, _ => none

/-- The exponential of `lnAbsGammaQuotEncl` at Ziv level `w`: the sign of `Γ(s)/Γ(x)` and a
positive enclosure of its absolute value. -/
def gammaQuotEnclOf (X S : Nat → Encl) (ex es : AzInt)
    (Fx Fs : Nat → Option (Bool × AzInt × Encl)) (w : Nat) : Option (Bool × Encl) :=
  (lnAbsGammaQuotEncl X S ex es Fx Fs (w + max (gammaLnBits ex) (gammaLnBits es)) w).bind
    fun r => (gammaExpEncl false r.2 w).map fun g => (r.1, g)

/-- `gammaQuotEnclOf` for floats `x`, `y`: the sign of `Γ(x + y)/Γ(x)` and a positive
enclosure of its absolute value. -/
def genPochCore (x y : AzFloat) (w : Nat) : Option (Bool × Encl) :=
  let ex := expOf x
  let ey := expOf y
  gammaQuotEnclOf (fun _ => Encl.exact x) (fun V => Encl.add V (Encl.exact x) (Encl.exact y))
    ex ((if ex ≤ ey then ey else ex) + 1) (gammaFloatFrac x) (betaSumFrac x y) w

/-! ### The driver -/

/-- `Γ(x + y)/Γ(x)` for finite `x`, `y` (zero included). -/
def genPochReal (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if isInteger y then
    if le zero y then pochReal x (truncToAzInt y).abs.toNat p mode
    else genPochNegInt x (truncToAzInt y).abs.toNat p mode
  else if isInteger x && le x zero then (zero, .eq)
  else if sumIsNonposInt x y then (nan, .eq)
  else if p = 0 then (nan, .eq)
  else
    zivLoop (fun w => gammaApproxOf (genPochCore x y w) w) p mode gammaFuel (max 64 (p + 32))

/-- `Γ(x + y)/Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` at a pole, for an infinite argument, for `p = 0` unless the value is `0`,
or if the fuel runs out). -/
def genPochhammerPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x, y with
  | nan, _ => (nan, .eq)
  | _, nan => (nan, .eq)
  | infinity _, _ => (nan, .eq)
  | _, infinity _ => (nan, .eq)
  | x, y => genPochReal x y p mode

/-- `Γ(x + y)/Γ(x)` rounded to nearest at the larger of the precisions of `x` and `y`. -/
def genPochhammer (x y : AzFloat) : AzFloat :=
  (genPochhammerPrecRound x y (max (x.precision?.getD 1) (y.precision?.getD 1)) .Nearest).1

end Azurite.AzFloat
