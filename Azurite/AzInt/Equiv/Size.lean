/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Size
import Azurite.AzInt.Equiv.Conversion
import Azurite.AzNat.Equiv.Size
import Azurite.BasuPollackRoy.Chapter8.Section8_1.Definition_8_4

namespace Azurite.AzInt

theorem size_toInt (z : AzInt) : z.toInt.natAbs.size = z.size := by
  unfold AzInt.size
  rw [← toNat_natAbs z, AzNat.size_toNat]
  rfl

theorem size_eq_int_size (z : AzInt) : z.size = BPR.Int.size z.toInt := by
  unfold BPR.Int.size
  exact size_toInt z |>.symm

theorem size_ofInt (i : Int) : (ofInt i).size = i.natAbs.size := by
  rw [← size_toInt, toInt_ofInt]

end Azurite.AzInt
