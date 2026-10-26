/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cbrt
import Azurite.AzFloat.SqrtRat
import Azurite.AzInt.DivMod

/-!
# Cube root of a rational

`∛q` for a rational `q = n / d`, correctly rounded to a destination precision `p` — the cube-root
analogue of `sqrtRatCore`.  With `e = ⌊log₂ (n / d)⌋` (sizes and one normalized comparison) and
`h = ⌊e / 3⌋`, the shift `3k` with `k = p − 1 − h` brings the quotient into
`[2^(3p−3), 2^(3p))`: `A / D = (n / d) · 2^(3k)`, applied to `n` or to `d` by the sign of `k`.
Then `∛(A / D) ∈ [2^(p−1), 2^p)` and
* its floor is the integer cube root of the integer quotient `⌊A / D⌋` (`AzNat.rootInt`),
  since `⌊∛⌊x⌋⌋ = ⌊∛x⌋` for every real `x ≥ 0`;
* it equals the floor `c` exactly iff `c³ · D = A`;
* it lies below, at or above the midpoint `c + 1/2` according to the comparison of `8A` with
  `(2c + 1)³ · D`.
Both comparisons are `AzNat.compareProduct`.  `roundFromFloor` gives the rounded integer and
the comparison tag, and the result is `∛(A / D) · 2^(−k)`, normalized with exponent
`h + 1 = p − k`.  A negative `q` is handled by the symmetry `∛(−q) = −∛q` with the rounding
mode negated and the comparison swapped; `∛0 = 0`.  `Equiv/CbrtRat.lean` proves
`cbrtRatPrecRound q p mode = roundVal p mode (Spec.cbrt q)`.
-/

namespace Azurite.AzFloat

/-- `∛(n / d)` for `n, d ≠ 0`, rounded to precision `p` with `mode`, and the comparison of the
result with the exact cube root. -/
def cbrtRatCore (n d : AzNat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  -- `e = ⌊log₂ (n / d)⌋`
  let e₀ : AzInt := (AzNat.ofNat n.size).toAzInt - (AzNat.ofNat d.size).toAzInt
  let e : AzInt :=
    if AzNat.normalizedCompare n d == .lt then e₀ - (AzNat.ofNat 1).toAzInt else e₀
  -- `h = ⌊e / 3⌋`, `k = p − 1 − h`
  let h₁ : AzInt := e / (AzNat.ofNat 3).toAzInt + (AzNat.ofNat 1).toAzInt
  let k : AzInt := (AzNat.ofNat p).toAzInt - h₁
  let sh : Nat := 3 * k.abs.toNat
  let A := if k.sign then n.shiftLeft sh else n
  let D := if k.sign then d else d.shiftLeft sh
  let c := AzNat.rootInt (A / D) 3
  let exact := AzNat.compareProduct (c.pow 3) D A == .eq
  let cmpMid :=
    (AzNat.compareProduct (((c.shiftLeft 1).addUInt64 1).pow 3) D (A.shiftLeft 3)).swap
  let ro := roundFromFloor c exact cmpMid mode
  (normalizeCarry (AzInt.mkNorm true ro.1) h₁ p, ro.2)

/-- The cube root of a rational, rounded to precision `p` with `mode`, and the comparison of the
result with the exact cube root. -/
def cbrtRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then (zero, .eq)
  else if p = 0 then (nan, .eq)
  else if q.sign then cbrtRatCore q.num q.den p mode
  else
    let r := cbrtRatCore q.num q.den p (-mode)
    (-r.1, r.2.swap)

/-- `∛q` rounded to nearest at precision `p`. -/
def cbrtRat (q : AzRat) (p : Nat) : AzFloat := (cbrtRatPrecRound q p .Nearest).1

end Azurite.AzFloat
