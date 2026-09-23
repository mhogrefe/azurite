/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proof for AzVector zero.
-/
import Azurite.AzVector.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} [Zero R] {n : Nat}

/-- Zero commutes with `toFn`. -/
@[simp]
theorem AzVector.toFn_zero' :
    (0 : AzVector R n).toFn = 0 := AzVector.toFn_zero

/-- Zero commutes with `ofFn`. -/
@[simp]
theorem AzVector.ofFn_zero :
    AzVector.ofFn (0 : Fin n → R) = (0 : AzVector R n) := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
