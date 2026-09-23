/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Pow

/-!
# Equivalence: AzNat exponentiation ↔ ℕ power

Both AzNat exponentiation algorithms — `AzNat.pow` (sliding-window) and `AzNat.powBinary`
(binary) — agree with `ℕ` exponentiation under `toNat`, and the two agree with each other.

The forward lemmas are one-line applications of the generic transports
`Azurite.map_slidingWindowPow` / `Azurite.map_fastPow` with `f = toNat`; the backward `ofNat_*`
lemmas then follow by `toNat` injectivity.

## Main theorems

- `toNat_pow`, `toNat_powBinary`: `(a.pow n).toNat = a.toNat ^ n` (and the binary analog).
- `pow_eq_powBinary`: the two algorithms compute the same value.
- `ofNat_pow`, `ofNat_powBinary`: `(ofNat m).pow n = ofNat (m ^ n)` (and the binary analog).
-/

namespace Azurite.AzNat

/-- Forward direction: `toNat` preserves `pow`. -/
@[simp] theorem toNat_pow (a : AzNat) (n : ℕ) : (a.pow n).toNat = a.toNat ^ n :=
  Azurite.map_slidingWindowPow AzNat.toNat toNat_one toNat_mul a n

/-- Forward direction: `toNat` preserves `powBinary`. -/
@[simp] theorem toNat_powBinary (a : AzNat) (n : ℕ) : (a.powBinary n).toNat = a.toNat ^ n :=
  Azurite.map_fastPow AzNat.toNat toNat_one toNat_mul a n

/-- The two exponentiation algorithms compute the same value. -/
theorem pow_eq_powBinary (a : AzNat) (n : ℕ) : a.pow n = a.powBinary n :=
  toNat_injective (by rw [toNat_pow, toNat_powBinary])

/-- Backward direction: `ofNat` preserves `pow`. -/
@[simp] theorem ofNat_pow (m n : ℕ) : (AzNat.ofNat m).pow n = AzNat.ofNat (m ^ n) :=
  toNat_injective (by rw [toNat_pow, toNat_ofNat, toNat_ofNat])

/-- Backward direction: `ofNat` preserves `powBinary`. -/
@[simp] theorem ofNat_powBinary (m n : ℕ) :
    (AzNat.ofNat m).powBinary n = AzNat.ofNat (m ^ n) :=
  toNat_injective (by rw [toNat_powBinary, toNat_ofNat, toNat_ofNat])

end Azurite.AzNat
