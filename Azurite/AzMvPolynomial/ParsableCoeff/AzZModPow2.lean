/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ParsableCoeff (AzZModPow2 k)` instance: routes through the shared decimal
  char-list facade in `Azurite.AzZModPow2.ParsableElement`.  The residue renders
  as digits only, so `ParsableCoeff.mkDigitOnly` discharges the syntax conditions.

  Needs `NeZero (1 : AzZModPow2 k)` (part of the `ParsableCoeff` signature), which
  holds exactly when `2^k > 1`, i.e. `k ≠ 0`; we provide it from `[NeZero k]`.
-/
import Azurite.AzMvPolynomial.ParsableCoeff
import Azurite.AzZModPow2.ParsableElement
import Azurite.AzZModPow2.Instances
import Azurite.AzZModPow2.Equiv.Basic

namespace Azurite

open AzPolynomial

namespace AzZModPow2

variable {k : Nat}

/-- For `k ≠ 0` the ring `ℤ / 2^k` is nontrivial, so `1 ≠ 0`. -/
instance instNeZeroOne [NeZero k] : NeZero (1 : AzZModPow2 k) := by
  have : Fact (1 < 2 ^ k) := ⟨Nat.one_lt_two_pow_iff.mpr (NeZero.ne k)⟩
  refine ⟨fun h => one_ne_zero (?_ : (1 : ZMod (2 ^ k)) = 0)⟩
  rw [← toZMod_one, ← toZMod_zero, h]

end AzZModPow2

instance {k : Nat} [NeZero k] : ParsableCoeff (AzZModPow2 k) :=
  ParsableCoeff.mkDigitOnly
    AzZModPow2.toChars
    AzZModPow2.parseChars
    AzZModPow2.parseChars_toChars
    AzZModPow2.toChars_ne_nil
    AzZModPow2.mem_toChars_digit
    AzZModPow2.toChars_zero

end Azurite
