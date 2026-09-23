/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.SplitHalves

namespace UInt64

/-- Full 128-bit product of two 64-bit unsigned integers, returned as `(hi, lo)`. -/
@[inline]
def wideMul (x y : UInt64) : UInt64 × UInt64 :=
  let (x₁, x₀) := splitInHalf x
  let (y₁, y₀) := splitInHalf y
  let x₀y₀ : UInt64 := x₀.toUInt64 * y₀.toUInt64
  let x₀y₁ : UInt64 := x₀.toUInt64 * y₁.toUInt64
  let x₁y₀ : UInt64 := x₁.toUInt64 * y₀.toUInt64
  let x₁y₁ : UInt64 := x₁.toUInt64 * y₁.toUInt64
  let (x₀y₀hi, x₀y₀lo) := splitInHalf x₀y₀
  let middle1 : UInt64 := x₀y₁ + x₀y₀hi.toUInt64
  let middle2 : UInt64 := middle1 + x₁y₀
  -- The carry into the high word is added as a conditional *scalar* rather
  -- than by branching on the result: keeping `(z₁, z₀)` out of conditional
  -- control flow lets codegen hold the pair in registers instead of boxing
  -- it at a control-flow join point.
  let carry : Bool := middle2 < middle1
  let x₁y₁' : UInt64 := x₁y₁ + (if carry then (1 : UInt64) <<< 32 else 0)
  let z₁ : UInt64 := x₁y₁' + wideHiHalf middle2
  let z₀ : UInt64 := joinHalves (loHalf middle2) x₀y₀lo
  (z₁, z₀)

end UInt64
