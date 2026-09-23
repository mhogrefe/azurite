/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Basic
import Azurite.AzInt.Conversion
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzNat.Equiv.Basic

/-!
# Conversions into `AzRat`

`AzNat.toAzRat n` represents the natural number `n` as the reduced fraction `n / 1`, and
`AzInt.toAzRat z` represents the integer `z` as `(sign z) · |z| / 1`. The primitive fixed-width
`UIntN`/`IntN`/`USize`/`ISize` types convert by delegating through `.toAzInt.toAzRat`, mirroring
the primitive `.toAzInt` conversions in `Azurite/AzInt/Conversion.lean`.

The `reduced` invariant `coprime · 1 = true` is discharged via `AzNat.coprime_iff` and
`Nat.coprime_one_right`.
-/

namespace Azurite.AzNat

/-- An `AzNat` as an `AzRat`: the reduced fraction `n / 1`. -/
def toAzRat (n : AzNat) : AzRat where
  sign := true
  num := n
  den := 1
  den_nz := by decide
  zero_sign := fun _ => rfl
  reduced := (AzNat.coprime_iff n 1).mpr (by rw [AzNat.toNat_one]; exact Nat.coprime_one_right _)

end Azurite.AzNat

namespace Azurite.AzInt

/-- An `AzInt` as an `AzRat`: the reduced fraction `|z| / 1` carrying `z`'s sign. -/
def toAzRat (z : AzInt) : AzRat where
  sign := z.sign
  num := z.abs
  den := 1
  den_nz := by decide
  zero_sign := z.zero_sign
  reduced := (AzNat.coprime_iff z.abs 1).mpr (by rw [AzNat.toNat_one]; exact Nat.coprime_one_right _)

end Azurite.AzInt

/-! ### Primitive fixed-width types (delegating through `AzInt`) -/

def UInt64.toAzRat (u : UInt64) : Azurite.AzRat := u.toAzInt.toAzRat
def UInt32.toAzRat (u : UInt32) : Azurite.AzRat := u.toAzInt.toAzRat
def UInt16.toAzRat (u : UInt16) : Azurite.AzRat := u.toAzInt.toAzRat
def UInt8.toAzRat (u : UInt8) : Azurite.AzRat := u.toAzInt.toAzRat
def USize.toAzRat (u : USize) : Azurite.AzRat := u.toAzInt.toAzRat

def Int64.toAzRat (i : Int64) : Azurite.AzRat := i.toAzInt.toAzRat
def Int32.toAzRat (i : Int32) : Azurite.AzRat := i.toAzInt.toAzRat
def Int16.toAzRat (i : Int16) : Azurite.AzRat := i.toAzInt.toAzRat
def Int8.toAzRat (i : Int8) : Azurite.AzRat := i.toAzInt.toAzRat
def ISize.toAzRat (i : ISize) : Azurite.AzRat := i.toAzInt.toAzRat
