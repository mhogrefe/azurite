/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Basic

/-!
# Tests for Newton–Barrett division

`divModNewton base U V` is compared with `Nat` division; `base = 2` forces the Newton recursion
down to two-limb reciprocals, so every path (the reciprocal recursion, its correction loop, the
Barrett corrections, the block loop with and without a partial top block, the normalization
shift) runs even on small inputs.  The last test crosses `divNewtonThreshold` so the dispatcher
itself takes the Newton path.
-/

namespace Azurite.AzNat

private def chk (base : Nat) (u v : Nat) : Bool :=
  let r := divModNewton base (ofNat u) (ofNat v)
  r.1.toNat == u / v && r.2.toNat == u % v

#guard chk 2 (2 ^ 640 + 12345) (2 ^ 320 + 1)
#guard chk 2 (2 ^ 1280 + 999) (2 ^ 640 + 17)
#guard chk 2 (2 ^ 2048 - 1) (2 ^ 512 + 7)
#guard chk 2 (3 ^ 1000) (7 ^ 100)
#guard chk 2 (2 ^ 5000 + 1) (2 ^ 4999 + 12345678901234567)
#guard chk 2 (2 ^ 5000 + 1) (2 ^ 4096 + 1)
#guard chk 3 (2 ^ 20000 + 5) (2 ^ 3001 - 1)
#guard chk 2 (2 ^ 999) (2 ^ 1000 + 1)
#guard chk 2 (2 ^ 1000 + 1) (2 ^ 1000 + 1)
#guard chk 2 (2 ^ 1023 + 2 ^ 500) (2 ^ 1023)
#guard chk 2 (2 ^ 130 - 1) (2 ^ 65 - 1)
#guard chk 2 (2 ^ 64 * 3) (2 ^ 64)
#guard chk 2 (7 ^ 2000 + 11 ^ 500) (13 ^ 300 + 1)
#guard chk 2 (2 ^ (64 * 17) + 3) (2 ^ (64 * 5) + 2 ^ (64 * 3) + 9)
#guard chk 2 (2 ^ (64 * 18) - 1) (2 ^ (64 * 6) - 1)
#guard (divModNewton 2 (ofNat 100) 0) == (0, ofNat 100)

-- Through the dispatcher: a divisor of 8200 limbs and a quotient of 49200 limbs take the Newton
-- path (`useNewtonDiv`).
#guard useNewtonDiv (ofNat (2 ^ (64 * 57400) + 3)) (ofNat (2 ^ (64 * 8200) + 5)) = true
#guard (ofNat (2 ^ (64 * 57400) + 3) / ofNat (2 ^ (64 * 8200) + 5)).toNat
  = (2 ^ (64 * 57400) + 3) / (2 ^ (64 * 8200) + 5)
#guard (ofNat (2 ^ (64 * 57400) + 3) % ofNat (2 ^ (64 * 8200) + 5)).toNat
  = (2 ^ (64 * 57400) + 3) % (2 ^ (64 * 8200) + 5)

end Azurite.AzNat
