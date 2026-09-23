/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.LowMask
import Azurite.AzInt.Equiv.Basic
import Azurite.AzNat.Equiv.LowMask

namespace Azurite.AzInt

theorem toInt_lowMask (k : Nat) : (AzInt.lowMask k).toInt = 2 ^ k - 1 := by
  unfold AzInt.lowMask toInt
  simp [AzNat.toNat_lowMask]

theorem lowMask_eq_ofInt (k : Nat) : AzInt.lowMask k = ofInt (2 ^ k - 1) := by
  have h : (AzInt.lowMask k).toInt = (ofInt (2 ^ k - 1)).toInt := by
    rw [toInt_lowMask, toInt_ofInt]
  exact ofInt_toInt (AzInt.lowMask k) ▸ ofInt_toInt (ofInt (2 ^ k - 1)) ▸ congrArg ofInt h

end Azurite.AzInt
