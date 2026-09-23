/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Square.Schoolbook
import Azurite.AzNat.Equiv.Square
import Azurite.AzNat.ModPow2
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.ParseBase

/-!
## `AzNat.squareSchoolbookModPow2` — low (mod `2 ^ k`) schoolbook squaring

The base of the low-squaring dispatch: the full schoolbook square (which already
exploits symmetry — it does `len·(len+1)/2` limb products, not `len²`) followed
by masking to the low `k` bits.  Used only for small operands, where forming the
full `2·len`-limb square and truncating is cheap; the top-half-skipping wins live
in the Karatsuba and Toom-Cook-3 passes.
-/

namespace Azurite.AzNat

/-- **Low schoolbook squaring.** `(a ^ 2) mod 2 ^ k`, via the full schoolbook
    square masked to the low `k` bits. -/
def squareSchoolbookModPow2 (a : AzNat) (k : Nat) : AzNat :=
  modPow2 (ofLimbs (schoolbookSquareLimbs a.limbs 0 a.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _))) k

theorem toNat_squareSchoolbookModPow2 (a : AzNat) (k : Nat) :
    (squareSchoolbookModPow2 a k).toNat = a.toNat ^ 2 % 2 ^ k := by
  unfold squareSchoolbookModPow2
  rw [toNat_modPow2, toNat_ofLimbs, schoolbookSquareLimbs_toNat, List.drop_zero,
    List.take_of_length_le (by rw [Array.length_toList]),
    show toNatLimbsList a.limbs.toList = a.toNat from rfl]

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def parse (s : String) : AzNat := (AzNat.parse s).get!

#guard (squareSchoolbookModPow2 (parse "7") 4).toNat == 49 % 16
#guard (squareSchoolbookModPow2 (parse "255") 8).toNat == 65025 % 256
#guard (squareSchoolbookModPow2 (parse "255") 16).toNat == 65025
#guard (squareSchoolbookModPow2 (parse "0") 32).toNat == 0
#guard (squareSchoolbookModPow2 (parse "123456789012345678901234567890") 200).toNat ==
  (123456789012345678901234567890 ^ 2) % (2 ^ 200)

end Tests
