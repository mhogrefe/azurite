/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Inv
import Azurite.AzZMod.Equiv.Inv
import Azurite.AzZMod.Instances
import Azurite.AzZMod.ToString
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.Basic

/-!
## `ℤ / p` is a field for prime `p`

When the modulus is prime, every nonzero residue is coprime to it, so the
extended-GCD inverse `AzZMod.inv` applies.  Packaging the total inverse `fieldInv`
(with the `0⁻¹ = 0` convention) yields a computable `Field (AzZMod p)`, hence the
`/` and `⁻¹` operations.  The field is pinned to `ZMod p.toNat` (a field by
`Fact (Nat.Prime p.toNat)`) through `toZMod`.
-/

namespace Azurite.AzZMod

variable {p : AzNat}

/-- A prime modulus is nonzero, so the residue-ring instances apply. -/
instance instNeZeroToNatOfPrime [Fact (Nat.Prime p.toNat)] : NeZero p.toNat :=
  ⟨(Fact.out (p := Nat.Prime p.toNat)).pos.ne'⟩

/-- Total inverse for a prime modulus: `0⁻¹ = 0`, and any nonzero residue is
coprime to the prime `p` (it lies in `(0, p)`), so its extended-GCD `inv` applies. -/
def fieldInv [Fact (Nat.Prime p.toNat)] (a : AzZMod p) : AzZMod p :=
  if h : a.val.limbs.size = 0 then 0
  else a.inv (by
    have hprime : Nat.Prime p.toNat := Fact.out
    have hpos : 0 < a.val.toNat :=
      Nat.pos_of_ne_zero (fun h0 => h ((AzNat.toNat_eq_zero_iff a.val).mp h0))
    exact ((hprime.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hpos a.isLt)).symm)

/-- **`ℤ / p` is a field** for prime `p`: every nonzero residue is invertible via
the extended-GCD `inv`, with the usual `0⁻¹ = 0` convention. -/
instance instField [Fact (Nat.Prime p.toNat)] : Field (AzZMod p) where
  inv := fieldInv
  exists_pair_ne := ⟨0, 1, by
    have : Fact (1 < p.toNat) := ⟨(Fact.out (p := Nat.Prime p.toNat)).one_lt⟩
    intro h
    have hz : toZMod (0 : AzZMod p) = toZMod (1 : AzZMod p) := by rw [h]
    rw [toZMod_zero, toZMod_one] at hz
    exact zero_ne_one hz⟩
  mul_inv_cancel a ha := by
    have hsz : a.val.limbs.size ≠ 0 := by
      intro h0
      apply ha
      apply ext
      rw [val_zero]
      apply AzNat.toNat_injective
      rw [(AzNat.toNat_eq_zero_iff a.val).mpr h0, AzNat.toNat_zero]
    show a * fieldInv a = 1
    unfold fieldInv
    rw [dite_eq_right hsz]
    exact mul_inv a _
  inv_zero := rfl
  nnqsmul := _
  qsmul := _

end Azurite.AzZMod

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZMod

private instance : Fact (Nat.Prime (AzNat.ofNat 7).toNat) := ⟨by rw [AzNat.toNat_ofNat]; decide⟩

-- In `ℤ/7`: `3⁻¹ = 5`, `1/3 = 5`, `6/2 = 3` (`2⁻¹ = 4`, `6·4 = 24 ≡ 3`).
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 7) 3)⁻¹) == "5"
#guard Azurite.AzZMod.toString
  (AzZMod.ofNat (AzNat.ofNat 7) 1 / AzZMod.ofNat (AzNat.ofNat 7) 3) == "5"
#guard Azurite.AzZMod.toString
  (AzZMod.ofNat (AzNat.ofNat 7) 6 / AzZMod.ofNat (AzNat.ofNat 7) 2) == "3"
-- `0⁻¹ = 0`.
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 7) 0)⁻¹) == "0"
-- `a / a = 1` for nonzero `a`.
#guard Azurite.AzZMod.toString
  (AzZMod.ofNat (AzNat.ofNat 7) 4 / AzZMod.ofNat (AzNat.ofNat 7) 4) == "1"

end Tests
