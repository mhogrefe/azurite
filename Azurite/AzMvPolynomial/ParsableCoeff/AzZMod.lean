/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ParsableCoeff (AzZMod m)` instance: routes through the shared decimal char-list
  facade in `Azurite.AzZMod.ParsableElement`.  The residue renders as digits only,
  so `ParsableCoeff.mkDigitOnly` discharges the syntax conditions.

  Needs `NeZero (1 : AzZMod m)` (part of the `ParsableCoeff` signature), which holds
  exactly when `1 < m.toNat`; we provide it from `[Fact (1 < m.toNat)]` (with
  `[NeZero m.toNat]` for the underlying ring), mirroring `ZMod`'s
  `[NeZero m] [Fact (1 < m)]`.
-/
import Azurite.AzMvPolynomial.ParsableCoeff
import Azurite.AzZMod.ParsableElement
import Azurite.AzZMod.Instances

namespace Azurite

open AzPolynomial

namespace AzZMod

variable {m : AzNat}

/-- For `1 < m.toNat` the ring `ℤ / m` is nontrivial, so `1 ≠ 0`. -/
instance instNeZeroOne [NeZero m.toNat] [Fact (1 < m.toNat)] : NeZero (1 : AzZMod m) := by
  refine ⟨fun h => one_ne_zero (?_ : (1 : ZMod m.toNat) = 0)⟩
  rw [← toZMod_one, ← toZMod_zero, h]

end AzZMod

instance {m : AzNat} [NeZero m.toNat] [Fact (1 < m.toNat)] : ParsableCoeff (AzZMod m) :=
  ParsableCoeff.mkDigitOnly
    AzZMod.toChars
    AzZMod.parseChars
    AzZMod.parseChars_toChars
    AzZMod.toChars_ne_nil
    AzZMod.mem_toChars_digit
    AzZMod.toChars_zero

end Azurite

section Tests
open Azurite Azurite.AzZMod

private instance : Fact (1 < (AzNat.ofNat 7).toNat) := ⟨by rw [AzNat.toNat_ofNat]; decide⟩

-- The coefficient facade renders/round-trips through `ParsableCoeff`.  `19 mod 7 = 5`.
#guard (String.ofList (ParsableCoeff.toChars (AzZMod.ofNat (AzNat.ofNat 7) 19))) == "5"
#guard ((ParsableCoeff.parseChars (ParsableCoeff.toChars (AzZMod.ofNat (AzNat.ofNat 7) 19))
  : Option (AzZMod (AzNat.ofNat 7))).map AzZMod.val) == some (AzZMod.ofNat (AzNat.ofNat 7) 5).val
end Tests
