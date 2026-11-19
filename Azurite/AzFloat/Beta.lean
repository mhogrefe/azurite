/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaBracket
import Azurite.AzFloat.RoundToInteger
import Azurite.AzFloat.Conversion
import Azurite.AzNat.Factorial
import Azurite.AzRat.Instances
import Azurite.AzRat.Div
import Azurite.AzInt.Pow
import Azurite.AzInt.SumProduct
import Azurite.AzInt.Instances

/-!
## The Beta function `B(a, b) = Γ(a) Γ(b) / Γ(a + b)`

`betaPrecRound a b p mode` is `B(a, b)` (DLMF §5.12) for floats `a`, `b`, rounded to precision
`p` in `mode`, with the comparison against the exact value; `beta a b` rounds to nearest at
the larger of the two precisions.

* **Special values**, following those of `Γ` (`AzFloat/Gamma.lean`).  `NaN` when `a` or `b` is
  `NaN`, `−∞`, or a negative integer (a pole of `Γ` where the sign is not determined).
  `B(+∞, b) = 0` for `b > 0` (and for `b = +∞`), `NaN` otherwise.  `B(0, b) = +∞` when `b` is
  not a negative integer (`Γ(0) = +∞`, the limit from the right: there is no negative zero).
  **`B(a, b) = 0` exactly when `a + b` is a non-positive integer** and neither `a` nor `b` is
  one (`1/Γ` vanishes there) — decided exactly by `sumIsNonposInt`.
* **Exact values**: `B(a, 1) = 1/a` and `B(1, b) = 1/b` are divisions; `B(a, n)` for a
  positive integer `n ≤ 64` and a short `a` is the rational number
  `(n − 1)! / (a (a + 1) ⋯ (a + n − 1))`, rounded directly (`betaSmallInt?`).
* **Rounding.**  Ziv's loop with fuel (`gammaFuel`) on `betaCore`
  (`AzFloat/BetaBracket.lean`).  The specification `betaPrecRound_eq_or`
  (`Equiv/Beta.lean`) is "correctly rounded, or `NaN`".  Besides the unknown arithmetic nature
  of the values: for a tiny `a`, `B(a, b) = 1/a − (ψ(b) + γ) + O(a)` needs about `|e|` bits
  beyond the precision when `1/a` is a float.
-/

namespace Azurite.AzFloat

/-- Is the value of `x` zero? -/
def isZeroVal (x : AzFloat) : Bool := le x zero && le zero x

/-- Is the value of `x` one? -/
def isOneVal (x : AzFloat) : Bool := le x one && le one x

/-- Is `x` a negative integer? -/
def isNegInt (x : AzFloat) : Bool := lt x zero && isInteger x

/-- Is `a + b` a non-positive integer?  For finite `a`, `b`.  When both are integers the sign of
the sum is one comparison.  When neither is, both are below `2` to their precision in absolute
value, so an integer sum is representable at `qa + qb + 2` bits: the sum is an integer exactly
when the addition at that precision is exact and gives one.  (The exact sum itself can be
astronomically long — `2^(−10⁹) + 3/2` — and is never formed.) -/
def sumIsNonposInt (a b : AzFloat) : Bool :=
  if isInteger a then isInteger b && le a (-b)
  else if isInteger b then false
  else
    let r := addPrecRound a b (a.precision?.getD 1 + b.precision?.getD 1 + 2) .Nearest
    if r.2 = .eq then isInteger r.1 && le r.1 zero else false

/-- The integer `∏_{j<n} (N + j D)`: the rising product of `N/D` times `D^n`, by a balanced
tree of pairwise products (`AzInt.product`). -/
def risingInt (N D : AzInt) (n : Nat) : AzInt :=
  AzInt.product ((List.range n).map fun (j : Nat) => N + (j : AzInt) * D)

/-- `B(N/D, n) = (n − 1)! Dⁿ / ∏_{j<n} (N + j D)` for a positive integer `n`, as one correctly
rounded division of two exact floats (a rational would cost a gcd of two long numbers). -/
def betaIntQuot (N D : AzInt) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  divPrecRound (ofAzInt ((AzNat.factorial (n - 1)).toAzInt * D.pow n))
    (ofAzInt (risingInt N D n)) p mode

/-- Is `a` short enough for the exact path: its precision and the size of its exponent
together at most `2p + 1024` bits? -/
def betaIntModerate (a : AzFloat) (p : Nat) : Bool :=
  match a with
  | finite _ e q _ _ => decide (q + e.abs.toNat ≤ 2 * p + 1024)
  | _ => false

/-- **`B(a, n)` for a positive integer `n ≤ 64`** and a short `a`: the rational number
`(n − 1)! / (a (a + 1) ⋯ (a + n − 1))`, rounded directly — no `Γ`, and no doubt left when the
value is a float.  With `a = N/D`, `D` a power of two, it is `betaIntQuot N D n`: the product
is taken on integers.  `none` when `b` is not such an
integer or `a` is not short. -/
def betaSmallInt? (a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if isInteger b && lt zero b && le b (ofAzNat (AzNat.ofNat 64)) && betaIntModerate a p then
    a.toAzRat?.map fun q =>
      let n := (truncToAzInt b).abs.toNat
      betaIntQuot (AzInt.mkNorm q.sign q.num) q.den.toAzInt n p mode
  else none

/-- The bracket of `B(a, b)` as a pair of `Roundable`s, strict on both sides; the dummy bracket
`[−1, 1]` when `betaCore` gives nothing. -/
def betaApprox (a b : AzFloat) (w : Nat) : Roundable × Roundable :=
  gammaApproxOf (betaCore a b w) w

/-- `B(a, b)` for finite `a`, `b` (zero included). -/
def betaReal (a b : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if isNegInt a || isNegInt b then (nan, .eq)
  else if isZeroVal a || isZeroVal b then (infinity true, .eq)
  else if p = 0 then (nan, .eq)
  else if isOneVal b then divPrecRound one a p mode
  else if isOneVal a then divPrecRound one b p mode
  else
    match betaSmallInt? a b p mode with
    | some r => r
    | none =>
      match betaSmallInt? b a p mode with
      | some r => r
      | none =>
        if sumIsNonposInt a b then (zero, .eq)
        else zivLoop (betaApprox a b) p mode (gammaFuel p) (max 64 (p + 32))

/-- `B(+∞, y)`: `0` for `y > 0`, `NaN` otherwise. -/
def betaInfinite (y : AzFloat) : AzFloat × Ordering :=
  if lt zero y then (zero, .eq) else (nan, .eq)

/-- `B(a, b)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` at a negative integer, for `p = 0` unless the value is `0` or `+∞`, or if the
fuel runs out). -/
def betaPrecRound (a b : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match a, b with
  | nan, _ => (nan, .eq)
  | _, nan => (nan, .eq)
  | infinity s, b => if s then betaInfinite b else (nan, .eq)
  | a, infinity s => if s then betaInfinite a else (nan, .eq)
  | a, b => betaReal a b p mode

/-- `B(a, b)` rounded to nearest at the larger of the precisions of `a` and `b`. -/
def beta (a b : AzFloat) : AzFloat :=
  (betaPrecRound a b (max (a.precision?.getD 1) (b.precision?.getD 1)) .Nearest).1

end Azurite.AzFloat
