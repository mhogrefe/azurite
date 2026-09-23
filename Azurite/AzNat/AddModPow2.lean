/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.ModPow2
import Azurite.UInt64.AddWithCarry

/-!
## `AzNat.addModPow2` — fused add-then-reduce mod `2 ^ k`

Walks the low `L = (k + 63) / 64` limbs of `a` and `b`, reading `0` past each
array's length (no padding allocation), adds with carry, drops the final
carry-out, and masks the result to the low `k` bits via `modPow2`.  This never
forms the extra carry-limb that `AzNat.add` appends.
-/

namespace Azurite.AzNat

/-- Build the low `L` limbs of `a + b` reading `0` past each array's length,
    pushing each carry-propagated limb onto `acc`; the final carry-out is
    dropped. -/
def lowSumLimbs (a b : Array UInt64) (L i : Nat) (carry : Bool)
    (acc : Array UInt64) : Array UInt64 :=
  if i < L then
    let awc := UInt64.addWithCarry (a.getD i 0) (b.getD i 0) carry
    lowSumLimbs a b L (i + 1) awc.2 (acc.push awc.1)
  else acc
termination_by L - i

/-- **Fused add-and-mask.** `(a + b) mod 2 ^ k`, computed by walking only the low
    `L = (k + 63) / 64` limbs of `a` and `b` (no carry-limb append, no padding)
    and masking to the low `k` bits.  Reads with allocation-free `Array.getD`
    (no `Option` boxing) into a buffer pre-sized to `L` limbs (no reallocation
    during the carry walk). -/
def addModPow2 (a b : AzNat) (k : Nat) : AzNat :=
  modPow2 (ofLimbs (lowSumLimbs a.limbs b.limbs ((k + 63) / 64) 0 false
    (Array.emptyWithCapacity ((k + 63) / 64)))) k

end Azurite.AzNat
