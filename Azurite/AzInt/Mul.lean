/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.MulSmall
import Azurite.AzNat.Mul

namespace Azurite.AzInt

/-- Multiply two `AzInt`s. -/
def mul (a b : AzInt) : AzInt :=
  mkNorm (a.sign == b.sign) (a.abs * b.abs)

instance : Mul AzInt := ⟨mul⟩

end Azurite.AzInt
