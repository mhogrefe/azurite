/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.SetBit

namespace Azurite.AzNat

/-- Set the `i`-th bit of `n` (0-indexed, LSB first) to `1`. Bit `i` lives in limb
`i / 64` at position `i % 64`; if that limb is beyond the array, zero limbs are
inserted and the set-bit limb appended. -/
def setBit (n : AzNat) (i : Nat) : AzNat :=
  let limbIdx := i / 64
  let bitIdx := i % 64
  if h : limbIdx < n.limbs.size then
    ofLimbs (n.limbs.set limbIdx ((n.limbs[limbIdx]).setBit bitIdx))
  else
    ofLimbs ((n.limbs ++ Array.replicate (limbIdx - n.limbs.size) (0 : UInt64)).push
              ((1 : UInt64) <<< UInt64.ofNat bitIdx))

end Azurite.AzNat
