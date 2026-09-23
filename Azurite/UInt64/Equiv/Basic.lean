/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.UInt

/-- `UInt64` values are equal iff their `toNat` images are equal. -/
lemma UInt64.eq_of_toNat_eq {x y : UInt64} (h : x.toNat = y.toNat) : x = y := by
  have h2 : x.toBitVec = y.toBitVec := BitVec.eq_of_toNat_eq h
  cases x; cases y; simp at h2; subst h2; rfl
