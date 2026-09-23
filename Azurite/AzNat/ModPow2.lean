/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs

namespace Azurite

/-- `modPow2 n k` returns `n mod 2 ^ k`, i.e. the lowest `k` bits of `n`.

    Examples: `modPow2 n 0 = 0`, `modPow2 n 1` is `1` if `n` is odd
    and `0` otherwise, `modPow2 n 64` is the lowest limb of `n`. Only
    examines the lowest `k / 64 + 1` limbs. -/
def AzNat.modPow2 (n : AzNat) (k : Nat) : AzNat :=
  let q := k / 64
  let r := k % 64
  if hq : q ≥ n.limbs.size then
    -- `2 ^ k` exceeds `n`'s bit-width; `n mod 2 ^ k = n`.
    n
  else if r = 0 then
    -- Take the first `q` limbs verbatim.
    AzNat.ofLimbs (n.limbs.extract 0 q)
  else
    -- Take the first `q` limbs and mask the `q`-th limb to `r` bits.
    have hlt : q < n.limbs.size := Nat.lt_of_not_le hq
    let lowLimbs := n.limbs.extract 0 q
    let mask := ((1 : UInt64) <<< UInt64.ofNat r) - 1
    let masked := n.limbs[q] &&& mask
    AzNat.ofLimbs (lowLimbs.push masked)

end Azurite
