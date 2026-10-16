/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RoundScaled
import Azurite.AzNat.CompareProduct
import Azurite.AzNat.NormalizedCompare
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Square
import Azurite.AzRat.Basic

/-!
# Square root and reciprocal square root of a rational

`√q` for a rational `q = n / d > 0`, correctly rounded to a destination precision `p`.  With
`e = ⌊log₂ (n / d)⌋` (read off the sizes and one normalized comparison, as in
`AzRat.floorLogBase2Abs`) and `h = ⌊e / 2⌋`, the even shift `2k` with `k = p − 1 − h` brings
the quotient into `[2^(2p−2), 2^(2p))`: `A / D = (n / d) · 2^(2k)`, where the shift is applied
to `n` or to `d` according to the sign of `k`.  Then `√(A / D) ∈ [2^(p−1), 2^p)` and

* its floor is the integer square root of the integer quotient `⌊A / D⌋`, since
  `⌊√⌊x⌋⌋ = ⌊√x⌋` for every real `x ≥ 0` — one division and one integer square root, with
  no reduction of the fraction;
* it equals the floor `s` exactly iff `s² · D = A`;
* it lies below, at or above the midpoint `s + 1/2` according to the comparison of `4A` with
  `(2s + 1)² · D`.

Both comparisons are `AzNat.compareProduct`, so they usually decide without multiplying.
`roundFromFloor` turns these facts into the rounded integer and the comparison tag, and the
result is `√(A / D) · 2^(−k)`, normalized with exponent `h + 1 = p − k`.  Negative inputs give
`NaN`, zero gives zero.  The reciprocal square root is the same core on the reciprocal fraction,
since `1 / √(n / d) = √(d / n)` exactly; `0 ↦ +∞`.  `Equiv/SqrtRat.lean` proves
`sqrtRatPrecRound q p mode = roundVal p mode (Spec.sqrt q)` and
`rsqrtRatPrecRound q p mode = roundVal p mode (Spec.rsqrt q)`.
-/

namespace Azurite.AzFloat

/-- `√(n / d)` for `n, d ≠ 0`, rounded to precision `p` with `mode`, and the comparison of the
result with the exact square root. -/
def sqrtRatCore (n d : AzNat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  -- `e = ⌊log₂ (n / d)⌋`
  let e₀ : AzInt := (AzNat.ofNat n.size).toAzInt - (AzNat.ofNat d.size).toAzInt
  let e : AzInt :=
    if AzNat.normalizedCompare n d == .lt then e₀ - (AzNat.ofNat 1).toAzInt else e₀
  -- `h = ⌊e / 2⌋`, `k = p − 1 − h`
  let h₁ : AzInt := e.shiftRight 1 + (AzNat.ofNat 1).toAzInt
  let k : AzInt := (AzNat.ofNat p).toAzInt - h₁
  let sh : Nat := 2 * k.abs.toNat
  let A := if k.sign then n.shiftLeft sh else n
  let D := if k.sign then d else d.shiftLeft sh
  let s := AzNat.sqrt (A / D)
  let exact := AzNat.compareProduct (AzNat.square s) D A == .eq
  let cmpMid :=
    (AzNat.compareProduct (AzNat.square ((s.shiftLeft 1).addUInt64 1)) D (A.shiftLeft 2)).swap
  let ro := roundFromFloor s exact cmpMid mode
  (normalizeCarry (AzInt.mkNorm true ro.1) h₁ p, ro.2)

/-- The square root of a rational, rounded to precision `p` with `mode`, and the comparison of
the result with the exact square root.  Negative inputs give `NaN`. -/
def sqrtRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then (zero, .eq)
  else if q.sign then sqrtRatCore q.num q.den p mode
  else (nan, .eq)

/-- The reciprocal square root of a rational, rounded to precision `p` with `mode`, and the
comparison of the result with the exact value.  `0 ↦ +∞`; negative inputs give `NaN`. -/
def rsqrtRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then (infinity true, .eq)
  else if q.sign then sqrtRatCore q.den q.num p mode
  else (nan, .eq)

end Azurite.AzFloat
