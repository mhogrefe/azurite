/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Beta

/-!
## Pochhammer's symbol `(x)ₙ = x (x + 1) ⋯ (x + n − 1)`

`pochhammerPrecRound x n p mode` is Pochhammer's symbol (the rising factorial, DLMF 5.2.4–5.2.5)
of a float `x` and a natural number `n`, rounded to precision `p` in `mode`, with the
comparison against the exact value; `pochhammer x n` rounds to nearest at the precision of `x`.
It is a polynomial in `x`: there are no poles.

* **Special values.**  `(x)₀ = 1` for every `x` but `NaN`, the infinities included.  For
  `n ≥ 1`: `(+∞)ₙ = +∞`, `(−∞)ₙ = (−1)ⁿ ∞`; **`0` exactly when a factor vanishes** — `x` an
  integer with `−n < x ≤ 0` (`pochHasZero`).
* **Exact path** (`pochExact?`): for `n ≤ 128` and a short `x = N/D`, or whenever the product
  is cheaper than the loop (`pochExactCheap`), the value is the rational `∏ (N + j D) / Dⁿ`,
  rounded by one division of two exact floats.  The product is taken on integers
  (`risingInt`).
* **Otherwise** Ziv's loop with fuel on `pochCore`, whose cost does not depend on `n`.  With
  `k` the number of negative factors (`pochSplit`),

    `(x)ₙ = (−1)^k · (1 − x − k)_k · (x + k)_{n−k}`,

  an identity for every `k ≤ n`; both rising factorials have a positive first factor, and
  `(y)ₘ = Γ(y + m)/Γ(y)` there.  Each ratio is `exp (St(y + m) − St(y)) · P(y)/P(y + m)` with
  the Stirling values and the rising products of the shifts of `ln Γ`
  (`stirlingShifted`, `AzFloat/BetaBracket.lean`): no reflection formula, no sine, no
  logarithm of the products, one exponential.  The pieces answer only when their arguments
  are positive, so a wrong `k` could only make the loop give up.
* **Contract** (`Equiv/Pochhammer.lean`): `pochhammerPrecRound_eq_or` — correctly rounded, or
  `(nan, .eq)` when the fuel runs out.  The value is a dyadic rational, which the loop cannot
  round when it is a float of the target precision or a boundary; the exact path takes those
  cases for `n ≤ 128` and for cheap products.
-/

namespace Azurite.AzFloat

/-- Does a factor of `(x)ₙ` vanish: is `x` an integer with `−n < x ≤ 0`? -/
def pochHasZero (x : AzFloat) (n : Nat) : Bool :=
  isInteger x && le x zero && lt (-(ofAzNat (AzNat.ofNat n))) x

/-- `(N/D)ₙ = ∏_{j<n} (N + j D) / Dⁿ` as one correctly rounded division of two exact
floats. -/
def pochIntQuot (N D : AzInt) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  divPrecRound (ofAzInt (risingInt N D n)) (ofAzInt (D.pow n)) p mode

/-- Is the exact product of `n` factors of `B` bits (numerator and denominator together)
cheaper than the loop at precision `p`?  With `ℓ` the number of limbs of a factor, the
balanced product and the division cost about `3·10⁻⁵ (n ℓ)^{3/2}` ms, the loop about as much
as `ln Γ` at `p` bits: 0.6 / 1.4 / 15 ms at 53 / 200 / 1000 bits (measured 2026-11-18). -/
def pochExactCheap (B n p : Nat) : Bool := decide (n * ((B + n.log2) / 64 + 1) ≤ 3 * p + 512)

/-- The bits of a float as a fraction: its precision and the size of its exponent. -/
def pochFloatBits (x : AzFloat) : Nat :=
  match x with
  | finite _ e q _ _ => q + e.abs.toNat
  | _ => 0

/-- **The exact path**: `(x)ₙ = ∏ (N + j D) / Dⁿ` for `x = N/D`, by one correctly rounded
division; `none` unless `n ≤ 128` and `x` is short (`betaIntModerate`), or the product is
cheap (`pochExactCheap`). -/
def pochExact? (x : AzFloat) (n p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  if (decide (n ≤ 128) && betaIntModerate x p) || pochExactCheap (pochFloatBits x) n p then
    x.toAzRat?.map fun q => pochIntQuot (AzInt.mkNorm q.sign q.num) q.den.toAzInt n p mode
  else none

/-- The number of negative factors of `(x)ₙ` for an `x` without a vanishing factor: `0` for
`x ≥ 0`, `n` for `x ≤ −n`, and `⌈−x⌉` in between. -/
def pochSplit (x : AzFloat) (n : Nat) : Nat :=
  if le zero x then 0
  else if le x (-(ofAzNat (AzNat.ofNat n))) then n
  else min n ((truncToAzInt x).abs.toNat + (if isInteger x then 0 else 1))

/-- `(t, q)` with `Γ(u)/Γ(v) = eᵗ q`, from enclosures `U`, `Vv` of `u, v > 0`: `t` the
difference of the Stirling values at the shifted arguments, `q` the quotient of the rising
products of the shifts; `none` unless both lower ends are positive. -/
def lnGammaDiff (U Vv : Encl) (L V M : Nat) (T : Array AzNat) (tol : AzFloat) :
    Option (Encl × Encl) :=
  if lt zero U.1 && lt zero Vv.1 then
    let ru := stirlingShifted U (expOf U.2) L V M T tol
    let rv := stirlingShifted Vv (expOf Vv.2) L V M T tol
    some (Encl.sub V ru.1 rv.1, Encl.div V rv.2 ru.2)
  else none

/-- `(neg, b)`: the sign of `(x)ₙ` and a positive enclosure `b` of `|(x)ₙ|` at Ziv level `w`,
for an argument given by its enclosures `X V` at the working precision `V`, split at `k ≤ n`
negative factors, with `bits` more bits for the size of `ln Γ`; `none` when a piece is
missing. -/
def pochCoreOf (X : Nat → Encl) (k n bits w : Nat) : Option (Bool × Encl) :=
  let wL := w + bits
  let L := lnGammaShiftExp wL
  let V := wL + 2 * L + 8 + 2 * wL.log2
  let M := lnGammaTerms wL (L + 1)
  let T := AzNat.tangentNumbers M
  let tol := powerOf2 (-(AzNat.ofNat (wL + 16)).toAzInt)
  let Y := Encl.sub V (Encl.exact one) (X V)
  let trivial : Option (Encl × Encl) := some (Encl.exact zero, Encl.exact one)
  match (if k = 0 then trivial else lnGammaDiff Y (Encl.sub V Y (Encl.nat k)) L V M T tol),
    (if n - k = 0 then trivial
      else lnGammaDiff (Encl.add V (X V) (Encl.nat n)) (Encl.add V (X V) (Encl.nat k)) L V M T
        tol) with
  | some (t₁, q₁), some (t₂, q₂) =>
    (gammaExpEncl false (Encl.add V t₁ t₂) w).map fun g =>
      (k % 2 == 1, Encl.mul V (Encl.mul V g q₁) q₂)
  | _, _ => none

/-- `pochCoreOf` for a float `x`. -/
def pochCore (x : AzFloat) (n w : Nat) : Option (Bool × Encl) :=
  pochCoreOf (fun _ => Encl.exact x) (pochSplit x n) n
    (gammaLnBits (expOf (addPrecRound x.abs (ofAzNat (AzNat.ofNat n)) 64 .Ceiling).1)) w

/-- The bracket of `(x)ₙ` as a pair of `Roundable`s, strict on both sides; the dummy bracket
`[−1, 1]` when `pochCore` gives nothing. -/
def pochApprox (x : AzFloat) (n w : Nat) : Roundable × Roundable :=
  gammaApproxOf (pochCore x n w) w

/-- `(x)ₙ` for a finite `x` (zero included) and `n ≥ 1`. -/
def pochReal (x : AzFloat) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if pochHasZero x n then (zero, .eq)
  else if p = 0 then (nan, .eq)
  else
    match pochExact? x n p mode with
    | some r => r
    | none => zivLoop (pochApprox x n) p mode gammaFuel (max 64 (p + 32))

/-- `(x)ₙ` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or infinite, or if the fuel runs out). -/
def pochhammerPrecRound (x : AzFloat) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | x =>
    if n = 0 then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
    else
      match x with
      | infinity s => (infinity (s || n % 2 == 0), .eq)
      | x => pochReal x n p mode

/-- `(x)ₙ` rounded to nearest at the precision of `x`. -/
def pochhammer (x : AzFloat) (n : Nat) : AzFloat :=
  (pochhammerPrecRound x n (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
