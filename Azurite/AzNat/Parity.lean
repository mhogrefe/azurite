/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic

namespace Azurite

/-- Efficient parity test: checks bit 0 of the lowest limb. -/
def AzNat.isEven (n : AzNat) : Bool :=
  if h : n.limbs.size > 0 then
    n.limbs[0] &&& 1 == 0
  else
    true

/-- Efficient parity test: checks bit 0 of the lowest limb. -/
def AzNat.isOdd (n : AzNat) : Bool :=
  !n.isEven

end Azurite
