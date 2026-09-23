/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.DivMod
import Azurite.Rounding.Basic

namespace UInt64

/-- Divide `x` by `y` rounding according to `mode`. Returns `(quotient, ord)`
where `ord` records how the rounded value relates to the true real value `x/y`:
`.lt` if quotient < x/y, `.eq` if equal, `.gt` if greater.

Uses `divMod` so the hardware `DIV` instruction is used once. An alternative
would be computing `remainder = x - quotient * other`; this version is one mul+sub
shorter and just as cache-friendly.

Behavior for `y = 0` is unspecified (`x / 0 = 0` at the `UInt64` level). -/
def divRound (x y : UInt64) (mode : Azurite.RoundingMode) :
    UInt64 × Ordering :=
  let (quotient, remainder) := x.divMod y
  if remainder == 0 then (quotient, .eq)
  else
    match mode with
    | .Floor | .Down => (quotient, .lt)
    | .Ceiling | .Up => (quotient + 1, .gt)
    | .Nearest =>
      match compare (y >>> 1) remainder with
      | .lt => (quotient + 1, .gt)
      | .gt => (quotient, .lt)
      | .eq =>
        -- `remainder = y >>> 1`: a genuine tie only when `y` is even.
        -- For odd `y`, `y >>> 1 = (y-1)/2 < y/2`, so this rounds down.
        if (y &&& 1 == 0) && (quotient &&& 1 == 1) then
          (quotient + 1, .gt)
        else
          (quotient, .lt)

end UInt64
