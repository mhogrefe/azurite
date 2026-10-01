/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.LogBase2
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

end Azurite.AzRat
