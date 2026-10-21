/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.LogBase2
import Azurite.AzRat.Unary
import Azurite.AzNat.LogBase
import Azurite.AzNat.Pow
import Azurite.AzNat.Mul
import Azurite.AzNat.Compare

/-!
# Floor of the base-`b` logarithm of `|q|`

`AzRat.floorLogBaseAbs b q = ⌊log_b |q|⌋` for `q ≠ 0` and a limb base `2 ≤ b`.  Malachite
estimates this with floating-point logarithms and corrects by one step; here the exponent is
bracketed from `⌊log₂ |q|⌋` and found by binary search on `b^e` versus `|q|`, so the
correctness proof (`Equiv/LogBase.lean`) is purely algebraic.  Powers of two take the exact
shortcut `⌊log₂ |q|⌋ / k` for `b = 2^k`.

The bracket: with `ℓ = ⌊log₂ |q|⌋`, `b^ℓ ≤ 2^ℓ ≤ |q|` when `ℓ < 0` and `1 ≤ |q|` when `0 ≤ ℓ`,
so `b^(min ℓ 0) ≤ |q|`; and `|q| < 2^(ℓ+1) ≤ b^(ℓ+1)` when `0 ≤ ℓ + 1`, `|q| < 1` otherwise, so
`|q| < b^(max (ℓ+1) 0)`.
-/

namespace Azurite.AzRat

/-- Compare `b^e` with `|q|` by cross-multiplication: `b^e` vs `num/den` is `den · b^e` vs `num`
for `e ≥ 0` and `den` vs `num · b^(−e)` for `e < 0`. -/
def cmpPowAbs (b : UInt64) (e : ℤ) (q : AzRat) : Ordering :=
  let bN := AzNat.ofNat b.toNat
  match e with
  | .ofNat n => AzNat.compare (q.den * bN.pow n) q.num
  | .negSucc n => AzNat.compare q.den (q.num * bN.pow (n + 1))

/-- Binary search for `⌊log_b |q|⌋` inside `[lo, hi)`, maintaining `b^lo ≤ |q| < b^hi`. -/
def floorLogSearch (b : UInt64) (q : AzRat) (lo hi : ℤ) : ℤ :=
  if _h : lo + 1 < hi then
    let mid := (lo + hi) / 2
    match cmpPowAbs b mid q with
    | .gt => floorLogSearch b q lo mid
    | _ => floorLogSearch b q mid hi
  else lo
  termination_by (hi - lo).toNat
  decreasing_by all_goals omega

/-- `⌊log_b |q|⌋` for `q ≠ 0` and `2 ≤ b` (returns `0` for `q = 0`). -/
def floorLogBaseAbs (b : UInt64) (q : AzRat) : ℤ :=
  if q.num = 0 then 0
  else
    let l := q.floorLogBase2Abs
    let k := b.toNat.log2
    if 2 ^ k = b.toNat then
      -- `b = 2^k`: `⌊log_{2^k} x⌋ = ⌊⌊log₂ x⌋ / k⌋`.
      l / (k : ℤ)
    else
      floorLogSearch b q (min l 0) (max (l + 1) 0)

/-- `⌈log_b |q|⌉` for `q ≠ 0` and `2 ≤ b` (returns `0` for `q = 0`, like `floorLogBaseAbs`):
the floor, plus one unless `|q|` is exactly `b^floor`. -/
def ceilingLogBaseAbs (b : UInt64) (q : AzRat) : ℤ :=
  if q.num = 0 then 0
  else
    let e := floorLogBaseAbs b q
    if cmpPowAbs b e q == .eq then e else e + 1

/-- `some e` if `|q| = b^e` (`e ∈ ℤ`), `none` otherwise (and for `q = 0`), for `2 ≤ b`. -/
def checkedLogBaseAbs (b : UInt64) (q : AzRat) : Option ℤ :=
  if q.num = 0 then none
  else
    let e := floorLogBaseAbs b q
    if cmpPowAbs b e q == .eq then some e else none


/-! ### Rational bases

`floorLogBaseRatAbs b q`, `ceilingLogBaseRatAbs b q` and `checkedLogBaseRatAbs b q` take a
rational base `b` (`none` unless `0 < b` and `b ≠ 1`, and for `q = 0`).  For `b > 1` the floor
is a binary search on the exponent with the exact comparison `cmpPowRatAbs` of `b^e` with
`|q|`; the bracket comes from a `Float` estimate of `log |q| / log b`, verified by two
comparisons, or else by doubling (`bracketHi`/`bracketLo`, with enough fuel for the base
`1 + 1/den b`).  A base in `(0, 1)` is handled through its reciprocal:
`⌊log_b x⌋ = −⌈log_{1/b} x⌉`. -/

/-- Compare `b^e` with `|q|` for a positive rational base `b`, by cross-multiplication:
`(num_b / den_b)^n` vs `num_q / den_q` is `num_b^n · den_q` vs `den_b^n · num_q`, and the
reciprocal for a negative exponent. -/
def cmpPowRatAbs (b : AzRat) (e : ℤ) (q : AzRat) : Ordering :=
  match e with
  | .ofNat n => AzNat.compare (b.num.pow n * q.den) (b.den.pow n * q.num)
  | .negSucc n => AzNat.compare (b.den.pow (n + 1) * q.den) (b.num.pow (n + 1) * q.num)

/-- Binary search for `⌊log_b |q|⌋` inside `[lo, hi)`, maintaining `b^lo ≤ |q| < b^hi`. -/
def floorLogSearchRat (b q : AzRat) (lo hi : ℤ) : ℤ :=
  if _h : lo + 1 < hi then
    let mid := (lo + hi) / 2
    match cmpPowRatAbs b mid q with
    | .gt => floorLogSearchRat b q lo mid
    | _ => floorLogSearchRat b q mid hi
  else lo
  termination_by (hi - lo).toNat
  decreasing_by all_goals omega

/-- The first of `hi, 2·hi, 4·hi, …` (at most `fuel` doublings) with `b^hi > |q|`, or the
last one. -/
def bracketHi (b q : AzRat) (hi : Nat) : Nat → Nat
  | 0 => hi
  | fuel + 1 => if cmpPowRatAbs b hi q == .gt then hi else bracketHi b q (2 * hi) fuel

/-- The first of `lo, 2·lo, 4·lo, …` (at most `fuel` doublings) with `b^(−lo) ≤ |q|`, or the
last one. -/
def bracketLo (b q : AzRat) (lo : Nat) : Nat → Nat
  | 0 => lo
  | fuel + 1 => if cmpPowRatAbs b (-(lo : ℤ)) q == .gt then bracketLo b q (2 * lo) fuel else lo

/-- A `Float` estimate of `⌊log_b |q|⌋` (any value is acceptable: the bracket built from it is
verified before use). -/
def estimateLogBaseRat (b q : AzRat) : ℤ :=
  let f := (AzNat.approxLog2 q.num - AzNat.approxLog2 q.den)
    / (AzNat.approxLog2 b.num - AzNat.approxLog2 b.den)
  if f < 0 then -((-f).toUInt64.toNat : ℤ) else (f.toUInt64.toNat : ℤ)

/-- Enough doublings for the brackets: `b^(2^fuel)` exceeds `|q|` and `1/|q|` when `b > 1`. -/
def bracketFuel (b q : AzRat) : Nat := b.den.size + q.num.size + q.den.size

/-- `⌊log_b |q|⌋` for a rational base `b > 1` and `q ≠ 0`. -/
def floorLogBaseRatAbsCore (b q : AzRat) : ℤ :=
  let e := estimateLogBaseRat b q
  if cmpPowRatAbs b (e - 1) q != .gt && cmpPowRatAbs b (e + 2) q == .gt then
    floorLogSearchRat b q (e - 1) (e + 2)
  else
    let F := bracketFuel b q
    let lo : ℤ := if q.den ≤ q.num then 0 else -(bracketLo b q 1 F : ℤ)
    let hi : ℤ := if q.den ≤ q.num then (bracketHi b q 1 F : ℤ) else 0
    floorLogSearchRat b q lo hi

/-- `⌈log_b |q|⌉` for a rational base `b > 1` and `q ≠ 0`. -/
def ceilingLogBaseRatAbsCore (b q : AzRat) : ℤ :=
  let e := floorLogBaseRatAbsCore b q
  if cmpPowRatAbs b e q == .eq then e else e + 1

/-- Is `b` a valid logarithm base: `0 < b` and `b ≠ 1`? -/
def isLogBase (b : AzRat) : Bool := b.sign && b.num != 0 && b.num != b.den

/-- `⌊log_b |q|⌋` for a rational base (`none` unless `0 < b`, `b ≠ 1` and `q ≠ 0`). -/
def floorLogBaseRatAbs (b q : AzRat) : Option ℤ :=
  if q.num = 0 ∨ ¬ isLogBase b then none
  else if b.den < b.num then some (floorLogBaseRatAbsCore b q)
  else some (-(ceilingLogBaseRatAbsCore b⁻¹ q))

/-- `⌈log_b |q|⌉` for a rational base (`none` unless `0 < b`, `b ≠ 1` and `q ≠ 0`). -/
def ceilingLogBaseRatAbs (b q : AzRat) : Option ℤ :=
  if q.num = 0 ∨ ¬ isLogBase b then none
  else if b.den < b.num then some (ceilingLogBaseRatAbsCore b q)
  else some (-(floorLogBaseRatAbsCore b⁻¹ q))

/-- `some e` if `|q| = b^e` for a rational base (`none` otherwise, and unless `0 < b`, `b ≠ 1`
and `q ≠ 0`). -/
def checkedLogBaseRatAbs (b q : AzRat) : Option ℤ :=
  if q.num = 0 ∨ ¬ isLogBase b then none
  else
    let b' := if b.den < b.num then b else b⁻¹
    let e := floorLogBaseRatAbsCore b' q
    if cmpPowRatAbs b' e q == .eq then some (if b.den < b.num then e else -e) else none


/-! ### Power-of-two bases

For the base `2^k` (`0 < k`), the base-2 exponents divided by `k`: floor division for the floor,
ceiling division for the ceiling, and divisibility for the checked logarithm (which, taking
`|q|`, ignores the sign). -/

/-- `⌊log_{2^k} |q|⌋` (`none` for `q = 0` or `k = 0`). -/
def floorLogBasePowerOf2Abs (q : AzRat) (k : Nat) : Option ℤ :=
  if q.num = 0 ∨ k = 0 then none else some (floorLogBase2Abs q / k)

/-- `⌈log_{2^k} |q|⌉` (`none` for `q = 0` or `k = 0`). -/
def ceilingLogBasePowerOf2Abs (q : AzRat) (k : Nat) : Option ℤ :=
  if q.num = 0 ∨ k = 0 then none else some (-((-ceilingLogBase2Abs q) / k))

/-- `some e` if `|q| = (2^k)^e`, `none` otherwise (and for `q = 0` or `k = 0`). -/
def checkedLogBasePowerOf2Abs (q : AzRat) (k : Nat) : Option ℤ :=
  if q.num = 0 ∨ k = 0 ∨ ¬ (q.num.isPowerOfTwo && q.den.isPowerOfTwo) then none
  else
    let e : ℤ := (q.num.size : ℤ) - q.den.size
    if e % k = 0 then some (e / k) else none

end Azurite.AzRat
