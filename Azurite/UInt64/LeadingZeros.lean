/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.Nat.Log

namespace UInt64

/-- Number of leading zero bits of a `UInt64`. For `d = 0`, returns `64`; for
    nonzero `d`, returns `63 - log2 d.toNat`, i.e. the unique `k ∈ [0, 63]`
    such that shifting `d` left by `k` puts the top bit at position 63. -/
@[inline]
def leadingZeros (d : UInt64) : Nat :=
  if d = 0 then 64 else 63 - d.toNat.log2

/-- For nonzero `d`, `leadingZeros d ≤ 63`. -/
theorem leadingZeros_le (d : UInt64) (hd : d ≠ 0) :
    leadingZeros d ≤ 63 := by
  unfold leadingZeros
  rw [ite_eq_right hd]
  exact Nat.sub_le _ _

end UInt64
