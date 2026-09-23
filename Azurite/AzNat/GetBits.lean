/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.ModPow2
import Azurite.AzNat.ShiftRight

namespace Azurite

/-- `getBitsAsLimb n i j h` extracts bits `[i, j)` of `n` as a single `UInt64`,
    given a proof that the width `j - i` fits in 64 bits. Equivalent to
    `(n >>> i).modPow2 (j - i)`, but computed without constructing an
    intermediate shifted `AzNat`: at most two limbs of `n` are read.

    Returns `0` when `i ≥ j` or when bit `i` is beyond `n`'s representation. -/
def AzNat.getBitsAsLimb (n : AzNat) (i j : Nat) (_h : j - i ≤ 64) : UInt64 :=
  if i ≥ j then 0
  else
    let q := i / 64
    let r := i % 64
    let width := j - i
    if hq : q ≥ n.limbs.size then 0
    else
      have hq_lt : q < n.limbs.size := Nat.lt_of_not_le hq
      let lowBits := n.limbs[q] >>> UInt64.ofNat r
      -- When `r + width > 64`, the high `r + width - 64` bits live in limb `q + 1`.
      let combined : UInt64 :=
        if r + width > 64 then
          if hq1 : q + 1 < n.limbs.size then
            lowBits ||| (n.limbs[q + 1] <<< UInt64.ofNat (64 - r))
          else
            lowBits  -- limb `q + 1` is implicitly zero
        else
          lowBits
      if width = 64 then combined
      else combined &&& (((1 : UInt64) <<< UInt64.ofNat width) - 1)

/-- `getBits n i j` extracts bits `[i, j)` of `n` as a fresh `AzNat`,
    equivalent to `(n >>> i).modPow2 (j - i)` but built limb-by-limb via
    `getBitsAsLimb`, avoiding the intermediate shifted-`AzNat` allocation. -/
def AzNat.getBits (n : AzNat) (i j : Nat) : AzNat :=
  if i ≥ j then 0
  else
    let width := j - i
    let numLimbs := (width + 63) / 64
    AzNat.ofLimbs ((Array.range numLimbs).map fun k =>
      n.getBitsAsLimb (i + k * 64) (min (i + k * 64 + 64) j) (by omega))

end Azurite
