/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- The high 32 bits of `u`, returned as a `UInt32`. -/
@[inline]
def hiHalf (u : UInt64) : UInt32 := (u >>> 32).toUInt32

/-- The low 32 bits of `u`, returned as a `UInt32`. -/
@[inline]
def loHalf (u : UInt64) : UInt32 := u.toUInt32

/-- The high 32 bits of `u`, returned in the low 32 bits of a `UInt64`. -/
@[inline]
def wideHiHalf (u : UInt64) : UInt64 := u >>> 32

/-- The low 32 bits of `u`, returned in the low 32 bits of a `UInt64`. -/
@[inline]
def wideLoHalf (u : UInt64) : UInt64 := u.toUInt32.toUInt64

/-- Split a `UInt64` into its high and low 32 bits, returned as `(hi, lo)`. -/
@[inline]
def splitInHalf (u : UInt64) : UInt32 × UInt32 :=
  (hiHalf u, loHalf u)

/-- Combine two 32-bit halves `hi` and `lo` into a single `UInt64`. -/
@[inline]
def joinHalves (hi lo : UInt32) : UInt64 :=
  (hi.toUInt64 <<< 32) ||| lo.toUInt64

end UInt64
