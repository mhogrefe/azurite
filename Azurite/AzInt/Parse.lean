/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.ToString
import Azurite.AzNat.ParseBase

namespace Azurite.AzInt

/-- Parse a `String` to `Option AzInt`. A leading `'-'` flips the sign;
    the resulting magnitude is parsed via `AzNat.parse` (decimal by
    default; a `"0b"`, `"0o"`, `"0x"` prefix on the magnitude
    auto-detects the base). Returns `none` on `"-0"` (no negative
    zero), the empty string, just-prefix input, or any invalid digit. -/
def parse (s : String) : Option AzInt :=
  if s.startsWith "-" then
    match AzNat.parse (s.drop 1).copy with
    | some n =>
      if h : n = 0 then none
      else some { sign := false, abs := n, zero_sign := fun h_abs => False.elim (h h_abs) }
    | none => none
  else
    match AzNat.parse s with
    | some n => some { sign := true, abs := n, zero_sign := fun _ => rfl }
    | none => none

end Azurite.AzInt

namespace Azurite

-- Sanity checks.

#guard (AzInt.parse "0").isSome
#guard (AzInt.parse "123").isSome
#guard (AzInt.parse "-123").isSome
#guard AzInt.parse "-0" = none
#guard AzInt.parse "" = none
#guard (AzInt.parse "0b101").isSome
#guard (AzInt.parse "0x10").isSome
#guard (AzInt.parse "18446744073709551616").isSome  -- 2^64 fits as AzInt
#guard (AzInt.parse "-18446744073709551616").isSome
end Azurite
