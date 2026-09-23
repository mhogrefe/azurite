/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Pow
import Azurite.AzZMod.Equiv.Basic

/-!
## Correctness of `AzZMod` exponentiation

`toZMod (a.pow n) = (toZMod a) ^ n` — a one-line application of the generic
sliding-window transport `Azurite.map_slidingWindowPow` with `f = toZMod`
(which preserves `1` and `*`).  Mirrors `AzZModPow2/Equiv/Pow.lean`.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- **Exponentiation agrees with `ZMod`.** -/
@[simp] theorem toZMod_pow [NeZero m.toNat] (a : AzZMod m) (n : ℕ) :
    toZMod (a.pow n) = (toZMod a) ^ n :=
  Azurite.map_slidingWindowPow toZMod toZMod_one toZMod_mul a n

/-- `ofZMod`-phrased companion. -/
@[simp] theorem ofZMod_pow [NeZero m.toNat] (z : ZMod m.toNat) (n : ℕ) :
    ofZMod (z ^ n) = (ofZMod z).pow n := by
  apply toZMod_injective
  rw [toZMod_pow, toZMod_ofZMod, toZMod_ofZMod]


end Azurite.AzZMod
