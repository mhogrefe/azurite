/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Pow2
import Azurite.AzNat.Size

/-!
# Base-2 logarithms of naturals

`floorLogBase2 n` and `ceilingLogBase2 n` are `⌊log₂ n⌋` and `⌈log₂ n⌉` (`none` for
`0`), from the bit length `size` and the power-of-two test `isPowerOfTwo`; `checkedLogBase2 n` is
`some k` when `n = 2^k` and `none` otherwise.  The same three for a power-of-two base
`2^k` (`floorLogBasePowerOf2`, `ceilingLogBasePowerOf2`, `checkedLogBasePowerOf2`; `none` for
the base `1`, i.e. `k = 0`) divide the base-2 exponents by `k`.
-/

namespace Azurite.AzNat

/-- `⌊log₂ n⌋` (`none` for `n = 0`): one less than the bit length. -/
def floorLogBase2 (n : AzNat) : Option Nat :=
  if n = 0 then none else some (n.size - 1)

/-- `⌈log₂ n⌉` (`none` for `n = 0`): one less than the bit length for a power of two, the bit
length otherwise. -/
def ceilingLogBase2 (n : AzNat) : Option Nat :=
  if n = 0 then none else if n.isPowerOfTwo then some (n.size - 1) else some n.size

/-- `some k` if `n = 2^k`, `none` otherwise. -/
def checkedLogBase2 (n : AzNat) : Option Nat :=
  if n.isPowerOfTwo then some (n.size - 1) else none

/-- `⌊log_{2^k} n⌋` (`none` for `n = 0` or `k = 0`). -/
def floorLogBasePowerOf2 (n : AzNat) (k : Nat) : Option Nat :=
  if k = 0 then none else n.floorLogBase2.map (· / k)

/-- `⌈log_{2^k} n⌉` (`none` for `n = 0` or `k = 0`). -/
def ceilingLogBasePowerOf2 (n : AzNat) (k : Nat) : Option Nat :=
  if k = 0 then none else n.ceilingLogBase2.map fun e => (e + k - 1) / k

/-- `some e` if `n = (2^k)^e`, `none` otherwise (and for `k = 0`). -/
def checkedLogBasePowerOf2 (n : AzNat) (k : Nat) : Option Nat :=
  if k = 0 then none
  else n.checkedLogBase2.bind fun e => if e % k = 0 then some (e / k) else none

end Azurite.AzNat
