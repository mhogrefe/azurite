/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZModPow2.Basic
import Azurite.AzNat.ToStringBase

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- Render the canonical residue as a decimal string (the decimal of `val`). -/
def toString (a : AzZModPow2 k) : String := AzNat.toString a.val

instance : ToString (AzZModPow2 k) := ⟨toString⟩

end Azurite.AzZModPow2

section Tests
open Azurite Azurite.AzZModPow2
-- `19 mod 16 = 3`; `200 < 256`.
#guard AzZModPow2.toString (AzZModPow2.ofNat 4 19) == "3"
#guard AzZModPow2.toString (AzZModPow2.ofNat 8 200) == "200"
#guard AzZModPow2.toString (AzZModPow2.ofNat 128 (2 ^ 128 - 1)) ==
  "340282366920938463463374607431768211455"
end Tests
