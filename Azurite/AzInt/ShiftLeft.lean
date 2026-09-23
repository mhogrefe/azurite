/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Basic
import Azurite.AzNat.ShiftLeft

namespace Azurite.AzInt

/-- Left shift: `z <<< sh`.  Preserves the sign of `z` and shifts the magnitude
    left by `sh` bits. -/
def shiftLeft (z : AzInt) (sh : Nat) : AzInt :=
  ⟨z.sign, z.abs <<< sh, fun h => z.zero_sign (AzNat.shiftLeft_eq_zero h)⟩

instance : HShiftLeft AzInt Nat AzInt := ⟨shiftLeft⟩

end Azurite.AzInt
