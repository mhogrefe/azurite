/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZModPow2.Basic
import Azurite.AzNat.ParseBase

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- Parse a decimal string and reduce it modulo `2^k`. Returns `none` exactly
when the underlying `AzNat.parse` fails; otherwise the value is masked to the
low `k` bits (so e.g.\ `"19"` parses to `3` in `ℤ/16`). -/
def parse (s : String) : Option (AzZModPow2 k) :=
  (AzNat.parse s).map (ofAzNat k)

end Azurite.AzZModPow2

section Tests
open Azurite Azurite.AzZModPow2
-- `"19"` reduces to `3` in `ℤ/16`; failure propagates as `none`.
#guard ((AzZModPow2.parse (k := 4) "19").map AzZModPow2.val) == some (AzNat.ofNat 3)
#guard ((AzZModPow2.parse (k := 8) "200").map AzZModPow2.val) == some (AzNat.ofNat 200)
#guard ((AzZModPow2.parse (k := 4) "not a number").map AzZModPow2.val) == none
end Tests
