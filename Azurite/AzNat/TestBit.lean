/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic
import Azurite.UInt64.TestBit

namespace Azurite.AzNat

/-- Return the `i`-th bit of `n` (0-indexed, LSB first). Bit `i` lives in limb
`i / 64` at position `i % 64`; returns `false` if that limb is beyond the array. -/
def testBit (n : AzNat) (i : Nat) : Bool :=
  let limbIdx := i / 64
  let bitIdx := i % 64
  if h : limbIdx < n.limbs.size then
    n.limbs[limbIdx].testBit bitIdx
  else
    false

end Azurite.AzNat
