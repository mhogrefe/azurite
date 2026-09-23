/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Basic
import Azurite.AzNat.ToStringBase

namespace Azurite.AzZMod

variable {m : AzNat}

/-- Render the canonical residue as a decimal string (the decimal of `val`). -/
def toString (a : AzZMod m) : String := AzNat.toString a.val

instance : ToString (AzZMod m) := ⟨toString⟩

end Azurite.AzZMod

section Tests
open Azurite Azurite.AzZMod
-- `19 mod 7 = 5`; `123456 mod 1000 = 456`.
#guard AzZMod.toString (AzZMod.ofNat (AzNat.ofNat 7) 19) == "5"
#guard AzZMod.toString (AzZMod.ofNat (AzNat.ofNat 1000) 123456) == "456"
end Tests
