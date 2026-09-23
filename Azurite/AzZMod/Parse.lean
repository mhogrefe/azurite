/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Basic
import Azurite.AzNat.ParseBase

namespace Azurite.AzZMod

/-- Parse a decimal string and reduce it modulo `m`. Returns `none` exactly
when the underlying `AzNat.parse` fails; otherwise the value is reduced into
`[0, m)` (so e.g.\ `"19"` parses to `5` in `ℤ/7`). -/
def parse {m : AzNat} [NeZero m.toNat] (s : String) : Option (AzZMod m) :=
  (AzNat.parse s).map (ofAzNat m)

end Azurite.AzZMod

section Tests
open Azurite Azurite.AzZMod
-- `"19"` reduces to `5` in `ℤ/7`; failure propagates as `none`.
#guard ((AzZMod.parse (m := AzNat.ofNat 7) "19").map AzZMod.val) == some (AzNat.ofNat 5)
#guard ((AzZMod.parse (m := AzNat.ofNat 1000) "123456").map AzZMod.val) == some (AzNat.ofNat 456)
#guard ((AzZMod.parse (m := AzNat.ofNat 7) "not a number").map AzZMod.val) == none
end Tests
