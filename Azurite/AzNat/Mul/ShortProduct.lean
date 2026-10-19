/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul
import Azurite.AzNat.Add
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.ModPow2

/-!
## Short products (MCA §3.3, Mulders)

`β = 2^64` is the limb base.

* `mulHigh n₀ A B n`, for `A, B < β^n`: an approximation `C'` of the high short product
  `C = ⌊A B / β^n⌋` with `C' ≤ C ≤ C' + 3(n − 1)` (MCA Algorithm 3.4 and Theorem 3.5).  The
  split is Mulders': `ℓ = ⌊3n/10⌋` low limbs, `k = n − ℓ`; `C₁` is the full product of the two
  high parts truncated, `C₂, C₃` the recursive short products of a low part by a high part; the
  `ℓ × ℓ` bottom corner is dropped.  Below `n₀` limbs the full product is truncated.
* `mulLow n₀ A B n`: the exact low product `A B mod β^n` by the mirror-image recursion (the
  `k × k` low product reduced, plus the recursive low products of a high part by a low part,
  shifted by `β^k`; the top corner vanishes modulo `β^n`).

Correctness: `Equiv/Mul/ShortProduct.lean`.  Both recursions are structural (fuel `n`).
-/

namespace Azurite.AzNat

/-- Mulders' split: the number of low limbs, `⌊3n/10⌋`. -/
def shortSplit (n : Nat) : Nat := 3 * n / 10

/-- MCA Algorithm 3.4 with explicit fuel. -/
def mulHighFuel (n₀ : Nat) : Nat → AzNat → AzNat → Nat → AzNat
  | 0, A, B, n => (A * B) >>> (64 * n)
  | fuel + 1, A, B, n =>
    if n ≤ n₀ then (A * B) >>> (64 * n)
    else
      let l := shortSplit n
      let k := n - l
      let C1 := ((A >>> (64 * l)) * (B >>> (64 * l))) >>> (64 * (k - l))
      let C2 := mulHighFuel n₀ fuel (A.modPow2 (64 * l)) (B >>> (64 * k)) l
      let C3 := mulHighFuel n₀ fuel (A >>> (64 * k)) (B.modPow2 (64 * l)) l
      C1 + C2 + C3

/-- **The high short product**: for `A, B < β^n`, within `3(n − 1)` of `⌊A B / β^n⌋` from
below. -/
def mulHigh (n₀ : Nat) (A B : AzNat) (n : Nat) : AzNat := mulHighFuel n₀ n A B n

/-- The low short product with explicit fuel. -/
def mulLowFuel (n₀ : Nat) : Nat → AzNat → AzNat → Nat → AzNat
  | 0, A, B, n => (A * B).modPow2 (64 * n)
  | fuel + 1, A, B, n =>
    if n ≤ n₀ then (A * B).modPow2 (64 * n)
    else
      let l := shortSplit n
      let k := n - l
      let C1 := ((A.modPow2 (64 * k)) * (B.modPow2 (64 * k))).modPow2 (64 * n)
      let C2 := mulLowFuel n₀ fuel (A >>> (64 * k)) (B.modPow2 (64 * l)) l
      let C3 := mulLowFuel n₀ fuel (A.modPow2 (64 * l)) (B >>> (64 * k)) l
      (C1 + ((C2 + C3) <<< (64 * k))).modPow2 (64 * n)

/-- **The low short product**: `A B mod β^n`, exactly. -/
def mulLow (n₀ : Nat) (A B : AzNat) (n : Nat) : AzNat := mulLowFuel n₀ n A B n

end Azurite.AzNat
